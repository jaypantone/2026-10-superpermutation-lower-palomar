#!/usr/bin/env python3
"""Exercise watchdog cleanup with harmless processes; never invoke Lean.

Run with ``python3 -B tools/test_resource_guard.py``. The tests retain the
production limits and trigger early stops using a temporary oversized log.
"""
from pathlib import Path
import os
import signal
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

import resource_guard as guard


class CleanupTests(unittest.TestCase):
    def run_guarded(self, code):
        with tempfile.TemporaryDirectory(prefix='proof-guard-test-') as tmp:
            root = Path(tmp)
            with guard.compiler_slot(root / 'test.lock'):
                return guard.run_checked([sys.executable, '-B', '-c', code],
                    cwd=root, env=os.environ.copy(), log_path=root / 'check.log')

    @staticmethod
    def noisy_sleep(fork=False):
        before = 'child = os.fork()\nif child == 0:\n time.sleep(20)\n os._exit(0)\n' if fork else ''
        return ('import os, time\n' + before +
                f"os.write(1, b'x' * {guard.LOG_LIMIT_BYTES + 1})\ntime.sleep(20)\n")

    def test_normal_success(self):
        result = self.run_guarded('pass')
        self.assertEqual(result.returncode, 0)
        self.assertIsNone(result.resource_report['stop_reason'])
        self.assertTrue(result.resource_report['cleanup'])

    def test_permission_fallback_kills_only_owned_positive_pids(self):
        unrelated = subprocess.Popen([sys.executable, '-B', '-c', 'import time; time.sleep(20)'],
                                     start_new_session=True)
        real_kill, real_killpg = os.kill, os.killpg
        try:
            with mock.patch.object(guard.os, 'killpg', side_effect=PermissionError('forced test denial')), \
                 mock.patch.object(guard.os, 'kill', side_effect=real_kill) as positive:
                result = self.run_guarded(self.noisy_sleep(fork=True))
                calls = [call.args[0] for call in positive.call_args_list]
            self.assertEqual(result.returncode, 125)
            self.assertIn('diagnostic-log size', result.resource_report['stop_reason'])
            events = result.resource_report['cleanup']
            self.assertTrue(any(e['method'] == 'permission-fallback-positive-pids' for e in events))
            self.assertGreaterEqual(len(set(calls)), 2)
            self.assertTrue(all(pid > 1 for pid in calls))
            self.assertNotIn(unrelated.pid, calls)
            self.assertIsNone(unrelated.poll())
            for event in events:
                self.assertFalse([m for m in guard.group_members(event['pgid'])
                                  if not m['state'].startswith('Z')])
        finally:
            if unrelated.poll() is None:
                real_killpg(unrelated.pid, signal.SIGKILL)
            unrelated.wait(timeout=3)

    def test_denial_after_group_is_killed_needs_no_pid_signal(self):
        real_killpg = os.killpg

        def kill_then_deny(pgid, sig):
            real_killpg(pgid, sig)
            raise PermissionError('forced denial after group became inactive')

        with mock.patch.object(guard.os, 'killpg', side_effect=kill_then_deny), \
             mock.patch.object(guard.os, 'kill') as positive:
            result = self.run_guarded(self.noisy_sleep())
        self.assertEqual(result.returncode, 125)
        positive.assert_not_called()
        self.assertTrue(any(e['method'] == 'permission-fallback-positive-pids'
                            and not e['signaled_pids'] for e in result.resource_report['cleanup']))

    def test_empty_group_needs_no_signal(self):
        proc = subprocess.Popen([sys.executable, '-B', '-c', 'pass'], start_new_session=True)
        proc.wait(timeout=3)
        with mock.patch.object(guard.os, 'killpg') as grouped, mock.patch.object(guard.os, 'kill') as positive:
            event = guard.kill_group(proc.pid)
        self.assertEqual(event['result'], 'no-live-members')
        grouped.assert_not_called()
        positive.assert_not_called()

    @staticmethod
    def member(uid=None, state='S', started='Thu Oct 22 00:00:00 2026'):
        return {'pid': 999999991, 'pgid': 999999991, 'uid': os.geteuid() if uid is None else uid,
                'state': state, 'started': started}

    def test_zombie_group_needs_no_signal(self):
        zombie = self.member(uid=os.geteuid() + 1, state='Z')
        with mock.patch.object(guard, 'group_members', return_value=[zombie]), \
             mock.patch.object(guard.os, 'killpg') as grouped, mock.patch.object(guard.os, 'kill') as positive:
            event = guard.kill_group(zombie['pgid'])
        self.assertEqual(event['result'], 'no-live-members')
        grouped.assert_not_called()
        positive.assert_not_called()

    def test_foreign_uid_is_not_signaled(self):
        foreign = self.member(uid=os.geteuid() + 1)
        with mock.patch.object(guard, 'group_members', return_value=[foreign]), \
             mock.patch.object(guard.time, 'monotonic', side_effect=[0, 3]), \
             mock.patch.object(guard.os, 'killpg') as grouped, mock.patch.object(guard.os, 'kill') as positive:
            with self.assertRaisesRegex(RuntimeError, 'Unable to stop owned process group'):
                guard.kill_group(foreign['pgid'])
        grouped.assert_not_called()
        positive.assert_not_called()

    def test_changed_pid_identity_is_not_signaled(self):
        original = self.member()
        replacement = self.member(started='Thu Oct 22 00:00:01 2026')

        def inspect(pgid, *, pid=None):
            return [original if pid is None else replacement]

        with mock.patch.object(guard, 'group_members', side_effect=inspect), \
             mock.patch.object(guard.os, 'killpg', side_effect=PermissionError('forced test denial')), \
             mock.patch.object(guard.os, 'kill') as positive:
            with self.assertRaisesRegex(RuntimeError, 'identity changed before cleanup signal'):
                guard.kill_group(original['pgid'], expected_leader=guard.process_identity(original))
        positive.assert_not_called()

    def test_failed_cleanup_still_restores_signal_handlers(self):
        before = {sig: signal.getsignal(sig) for sig in (signal.SIGINT, signal.SIGTERM)}
        with mock.patch.object(guard, 'kill_group', side_effect=RuntimeError('forced cleanup failure')):
            with self.assertRaisesRegex(RuntimeError, 'forced cleanup failure'):
                self.run_guarded('pass')
        self.assertEqual(before, {sig: signal.getsignal(sig) for sig in before})


if __name__ == '__main__':
    unittest.main(verbosity=2)
