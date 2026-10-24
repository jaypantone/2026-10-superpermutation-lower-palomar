"""Check selected Lean results sequentially using existing shared dependencies.

No downloads and no local dependency copies. --fresh ignores this project's
verified object cache. A timeout is an inconclusive stopped build.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import json
import os
import re
import time
from resource_guard import serialized, run_checked, staged_outputs, LEAN_MEMORY_MIB
from shared_setup import ROOT, PROOFS, prepare_workspace, runtime_config, sha
from proof_sources import (sources, graph, keys, source_relative, object_path,
                           artifacts, runtime_artifacts, atomic_json)


@serialized
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('targets', nargs='+')
    parser.add_argument('--fresh', action='store_true')
    parser.add_argument('--refresh-targets', action='store_true',
                        help='Recompile only explicitly requested targets; reuse verified dependencies.')
    parser.add_argument('--receipt', default='build.json',
                        help='Receipt filename in the external workspace, not in the source checkout.')
    args = parser.parse_args()
    loc = prepare_workspace()
    cfg = runtime_config()
    inventory = sources()
    from source_policy import validate_sources
    validate_sources(inventory)
    order, deps = graph(args.targets, inventory)
    lean = Path(cfg['lean'])
    compiler, runtime = sha(lean), runtime_artifacts(lean)
    frozen, closure_keys = keys(order, deps, inventory, compiler, cfg['external_lean_paths'])
    lib, logs = loc['build']/'lib', loc['build']/'logs'
    lib.mkdir(parents=True, exist_ok=True)
    logs.mkdir(parents=True, exist_ok=True)
    verification = loc['workspace']/'verification'
    result_path = (verification/args.receipt).resolve()
    if not result_path.is_relative_to(verification):
        raise RuntimeError('Build receipts must be inside the external verification directory')
    report = {'status': 'RUNNING', 'started_utc': datetime.now(timezone.utc).isoformat(),
              'targets': args.targets, 'compiler': str(lean), 'compiler_sha256': compiler,
              'runtime_artifacts': runtime, 'external_lean_paths': cfg['external_lean_paths'],
              'local_sources': frozen, 'results': [],
              'scope': 'Current repository source closure; pinned shared libraries reused.'}
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(lib)]+cfg['external_lean_paths']),
               OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', LEAN_NUM_THREADS='1',
               MATHLIB_CACHE_DIR=str(loc['shared']/'downloads'))
    atomic_json(result_path, report)
    for name in order:
        source = inventory[name]
        obj = object_path(lib, name)
        stamp = obj.with_suffix('.build.json')
        log = logs/(name+'.log')
        if (not args.fresh and not (args.refresh_targets and name in args.targets)
            and obj.exists() and stamp.exists() and not obj.with_suffix('.publishing.json').exists()):
            old = json.loads(stamp.read_text())
            requires_log = name in args.targets or '#print axioms' in source.read_text()
            valid_log = not requires_log or (log.is_file() and sha(log) == old.get('log_sha256'))
            if (old.get('key') == closure_keys[name] and old.get('runtime_artifacts') == runtime
                and old.get('artifacts') == artifacts(obj) and valid_log):
                report['results'].append({'module': name, 'status': 'REUSED_VERIFIED',
                    'key': closure_keys[name], 'artifacts': old['artifacts'],
                    'log_sha256': old.get('log_sha256')})
                continue
        obj.parent.mkdir(parents=True, exist_ok=True)
        with staged_outputs(obj) as (staged, publish):
            cmd = ['nice', '-n', '10', str(lean), '-j1', f'-M{LEAN_MEMORY_MIB}',
                   '-o', str(staged), '-i', str(staged.with_suffix('.ilean'))]
            cmd.append(str(source_relative(source)))
            staged_source = loc['sources']/source_relative(source)
            if sha(staged_source) != frozen[name] or sha(source) != frozen[name]:
                raise RuntimeError('Source changed after staging: ' + name)
            start = time.monotonic()
            run = run_checked(cmd, cwd=loc['sources'], env=env, log_path=log)
            if run.returncode == 0:
                publish()
        entry = {'module': name, 'status': 'PASSED' if run.returncode == 0 else 'FAILED',
                 'command': cmd, 'exit_code': run.returncode,
                 'seconds': round(time.monotonic()-start, 3), 'key': closure_keys[name],
                 'source_sha256': frozen[name], 'log_sha256': sha(log),
                 'resource_guard': run.resource_report}
        report['results'].append(entry)
        if run.returncode != 0:
            report['status'] = 'FAILED'
            atomic_json(result_path, report)
            print(run.stdout)
            return run.returncode
        bundle = artifacts(obj)
        atomic_json(stamp, {'key': closure_keys[name], 'olean_sha256': sha(obj),
            'artifacts': bundle, 'runtime_artifacts': runtime, 'log_sha256': sha(log)})
        entry['artifacts'] = bundle
        atomic_json(result_path, report)
        print(f'{name}: checked in {entry["seconds"]}s', flush=True)
    if any(sha(inventory[n]) != frozen[n] for n in order) or runtime_artifacts(lean) != runtime:
        raise RuntimeError('Source or compiler implementation changed during checking')
    report.update(status='PASS', finished_utc=datetime.now(timezone.utc).isoformat())
    atomic_json(result_path, report)
    print(f'PASS: {len(order)} source modules checked; this is not a Comparator/NanoDa result.')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
