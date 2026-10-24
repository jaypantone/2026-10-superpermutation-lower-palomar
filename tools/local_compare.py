"""Run bounded, unsandboxed local Comparator/NanoDa diagnostics after a build.

This is NOT the protected Linux Palomar verifier and never reports registry
acceptance. It neither builds proofs nor fetches dependencies. Existing build
receipts and object hashes must cover both selected environments. Export files,
logs, and diagnostic receipts stay in the external shared workspace.
"""
from pathlib import Path
from datetime import datetime, timezone
import argparse
import json
import os
import re
import resource
import sys

from resource_guard import serialized, run_checked, TIMEOUT_SECONDS, MAX_TIMEOUT_SECONDS
from shared_setup import ROOT, runtime_config, validate_dependencies, sha
from proof_sources import (sources, graph, keys, object_path, artifacts,
                           runtime_artifacts, atomic_json)

STANDARD_AXIOMS = {'propext', 'Classical.choice', 'Quot.sound'}
MAX_EXPORT_BYTES = 2 * 1024**3
ACTIVE_REPORT = None


def unique_object(pairs):
    d = {}
    for k, v in pairs:
        if k in d:
            raise RuntimeError('Duplicate JSON key: ' + k)
        d[k] = v
    return d


def read_configuration(path):
    d = json.loads(path.read_text(), object_pairs_hook=unique_object)
    required = {'challenge_module', 'solution_module', 'theorem_names', 'permitted_axioms'}
    allowed = required | {'definition_names', 'enable_nanoda'}
    if not isinstance(d, dict) or not required <= d.keys() or not d.keys() <= allowed:
        raise RuntimeError('Unsupported Comparator configuration shape')
    if d['challenge_module'] == d['solution_module']:
        raise RuntimeError('Challenge and Solution must be distinct environments')
    if not isinstance(d['theorem_names'], list) or not d['theorem_names']:
        raise RuntimeError('No theorem declarations selected')
    if d.get('definition_names'):
        raise RuntimeError('This helper permits no definition holes')
    if set(d['permitted_axioms']) != STANDARD_AXIOMS:
        raise RuntimeError('Expected exactly the three standard axioms')
    for name in [d['challenge_module'], d['solution_module'], *d['theorem_names']]:
        if not isinstance(name, str) or not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', name):
            raise RuntimeError('Unsupported declaration or module name')
    return d


def primitive_targets(prefix):
    """Read the actual pinned Comparator's literal list, failing on API drift."""
    path = prefix / 'src/lean/lake/Lake/CLI/Check.lean'
    source = path.read_text()
    match = re.search(r'^def primitiveTargets[^\n]*\n(.*?)^def ', source, re.M | re.S)
    if not match:
        raise RuntimeError('Cannot identify pinned Comparator primitive targets')
    body = re.sub(r'/\-.*?\-/', '', match[1], flags=re.S)
    body = '\n'.join(x.split('--', 1)[0] for x in body.splitlines())
    literal = re.fullmatch(r'\s*return\s*#\[([^\[\]]*)\]\s*', body)
    if not literal:
        raise RuntimeError('Unrecognized Comparator primitive target list')
    names = []
    for item in literal[1].split(','):
        if not item.strip():
            continue
        m = re.fullmatch(r'``([A-Za-z_][A-Za-z0-9_\'.]*)', item.strip())
        if not m:
            raise RuntimeError('Unrecognized primitive target expression')
        names.append(m[1])
    if not names or len(names) != len(set(names)):
        raise RuntimeError('Invalid Comparator primitive target list')
    builtin = re.search(r'^def builtinTargets[^\n]*\n(.*?)^def ', source, re.M | re.S)
    expected = ['Quot', 'Quot.mk', 'Quot.lift', 'Quot.ind']
    if not builtin or re.findall(r'``([A-Za-z_][A-Za-z0-9_.]*)', builtin[1]) != ['Quot.sound', *expected]:
        raise RuntimeError('Unrecognized Comparator quotient targets')
    return names, expected, path


def checked_objects(loc, cfg, modules, receipt_names):
    inventory = sources()
    from source_policy import validate_sources
    validate_sources(inventory)
    order, deps = graph(modules, inventory)
    lean = Path(cfg['lean'])
    compiler, runtime = sha(lean), runtime_artifacts(lean)
    frozen, closure_keys = keys(order, deps, inventory, compiler, cfg['external_lean_paths'])
    verification = (loc['workspace'] / 'verification').resolve()
    coverage, receipt_records = {}, []
    for name in receipt_names:
        path = (verification / name).resolve()
        if not path.is_relative_to(verification):
            raise RuntimeError('Build receipt must be in the external verification directory')
        receipt = json.loads(path.read_text())
        if receipt.get('status') != 'PASS' or receipt.get('compiler_sha256') != compiler:
            raise RuntimeError('Build receipt is not a successful current-compiler build: ' + name)
        if receipt.get('runtime_artifacts') != runtime or receipt.get('external_lean_paths') != cfg['external_lean_paths']:
            raise RuntimeError('Build receipt has a different runtime/dependency environment')
        for module, digest in receipt['local_sources'].items():
            if module in frozen and frozen[module] != digest:
                raise RuntimeError('Build receipt source is stale: ' + module)
            if module in frozen:
                coverage[module] = digest
        receipt_records.append({'path': str(path), 'sha256': sha(path)})
    if not set(order) <= coverage.keys():
        missing = sorted(set(order) - coverage.keys())
        raise RuntimeError('Build receipts do not cover selected source closure: ' + ', '.join(missing[:8]))
    lib = loc['build'] / 'lib'
    object_records = {}
    for module in order:
        obj = object_path(lib, module)
        stamp = obj.with_suffix('.build.json')
        if obj.with_suffix('.publishing.json').exists():
            raise RuntimeError('Object publication was interrupted: ' + module)
        record = json.loads(stamp.read_text())
        bundle = artifacts(obj)
        if record.get('key') != closure_keys[module] or record.get('runtime_artifacts') != runtime or record.get('artifacts') != bundle:
            raise RuntimeError('Compiled object does not match the current proof source: ' + module)
        object_records[module] = {'key': closure_keys[module], 'artifacts': bundle}
    return {'source_sha256': frozen, 'objects': object_records,
            'compiler_sha256': compiler, 'runtime_artifacts': runtime,
            'build_receipts': receipt_records}, inventory


def export_worker(output, command):
    """Redirect only export stdout; the outer process-group watchdog stays active."""
    resource.setrlimit(resource.RLIMIT_FSIZE, (MAX_EXPORT_BYTES, MAX_EXPORT_BYTES))
    with open(output, 'xb', buffering=0) as handle:
        os.dup2(handle.fileno(), 1)
    os.execvpe(command[0], command, os.environ)


@serialized
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('configuration', nargs='?', default='comparator.json')
    parser.add_argument('--build-receipt', action='append', help='External successful receipt filename; repeat to combine builds.')
    parser.add_argument('--kernel-timeout-seconds', type=int, default=TIMEOUT_SECONDS,
                        help=f'Explicit per-kernel-check deadline ({TIMEOUT_SECONDS}–{MAX_TIMEOUT_SECONDS}s); exports retain {TIMEOUT_SECONDS}s.')
    args = parser.parse_args()
    if not TIMEOUT_SECONDS <= args.kernel_timeout_seconds <= MAX_TIMEOUT_SECONDS:
        parser.error(f'--kernel-timeout-seconds must be between {TIMEOUT_SECONDS} and {MAX_TIMEOUT_SECONDS}')
    candidate = ROOT / args.configuration
    config_path = candidate.resolve()
    if not config_path.is_relative_to(ROOT) or candidate.is_symlink() or not candidate.is_file():
        raise RuntimeError('Configuration must be a regular file in this repository')
    selected = read_configuration(config_path)
    config_hash = sha(config_path)
    loc = validate_dependencies()
    cfg = runtime_config()
    evidence, inventory = checked_objects(loc, cfg,
        [selected['challenge_module'], selected['solution_module']], args.build_receipt or ['build.json'])
    prefix = Path(cfg['lean']).parent.parent
    primitives, builtin, check_source = primitive_targets(prefix)
    targets = builtin + selected['theorem_names'] + selected['permitted_axioms'] + primitives
    for executable in ('leanexport', 'lake', 'leanchecker', 'nanoda_bin'):
        if not os.access(prefix / 'bin' / executable, os.X_OK):
            raise RuntimeError('Pinned toolchain does not supply executable ' + executable)
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S') + '-' + str(os.getpid())
    out = loc['workspace'] / 'verification' / ('local-comparator-' + config_path.stem + '-' + stamp)
    out.mkdir(parents=True, exist_ok=False)
    report_path = out / 'report.json'
    report = {'status': 'RUNNING', 'scope': 'Unsandboxed local diagnostics; NOT full Palomar mechanical verification.',
              'configuration': str(config_path), 'configuration_sha256': config_hash,
              'started_utc': datetime.now(timezone.utc).isoformat(), 'evidence': evidence,
              'comparator_source_sha256': sha(check_source), 'export_targets': targets,
              'tool_sha256': {n: sha(prefix/'bin'/n) for n in ('leanexport', 'lake', 'leanchecker', 'nanoda_bin')},
              'driver_sha256': {n: sha(Path(__file__).with_name(n)) for n in ('local_compare.py', 'resource_guard.py')},
              'export_timeout_seconds': TIMEOUT_SECONDS, 'kernel_timeout_seconds': args.kernel_timeout_seconds,
              'export_size_limit_bytes': MAX_EXPORT_BYTES, 'steps': []}
    global ACTIVE_REPORT
    ACTIVE_REPORT = (report_path, report)
    atomic_json(report_path, report)
    env = dict(os.environ, LEAN_PATH=os.pathsep.join([str(loc['build']/'lib')] + cfg['external_lean_paths']),
               PATH=str(prefix/'bin') + os.pathsep + os.environ.get('PATH', ''),
               LEAN_NUM_THREADS='1', OMP_NUM_THREADS='1', OPENBLAS_NUM_THREADS='1', LEAN_ABORT_ON_PANIC='1')

    def run(label, cmd, *, timeout_seconds=TIMEOUT_SECONDS):
        log = out / (label + '.log')
        result = run_checked(['nice', '-n', '10', *cmd], cwd=loc['sources'], env=env, log_path=log,
                             timeout_seconds=timeout_seconds)
        report['steps'].append({'step': label, 'command': cmd, 'exit_code': result.returncode,
                                'log': str(log), 'log_sha256': sha(log), 'resource_guard': result.resource_report})
        atomic_json(report_path, report)
        if result.returncode:
            report['status'] = 'INCOMPLETE'
            report['stopped_at'] = label
            report['interpretation'] = 'No complete diagnostic success; timeouts and resource stops are inconclusive.'
            report['finished_utc'] = datetime.now(timezone.utc).isoformat()
            atomic_json(report_path, report)
            print(result.stdout[-4000:])
            return False
        return True

    exported = {}
    for kind in ('challenge', 'solution'):
        module = selected[kind + '_module']
        partial = out / (kind + '.ndjson.partial')
        export = out / (kind + '.ndjson')
        command = [str(prefix/'bin/leanexport'), module, '--', *targets]
        worker = [sys.executable, '-B', str(Path(__file__).resolve()), '--export-worker', str(partial), *command]
        if not run('export-' + kind, worker):
            return 1
        if not partial.is_file() or not 0 < partial.stat().st_size <= MAX_EXPORT_BYTES:
            raise RuntimeError('Exporter succeeded without a nonempty bounded export')
        partial.replace(export)
        exported[kind] = export
        report[kind + '_export'] = {'path': str(export), 'bytes': export.stat().st_size, 'sha256': sha(export)}
        atomic_json(report_path, report)
    comparison = dict(selected, enable_nanoda=False)
    diagnostic_config = out / 'comparator-local.json'
    atomic_json(diagnostic_config, comparison)
    if not run('comparator-and-lean-kernel', [str(prefix/'bin/lake'), 'comparator', '--config', str(diagnostic_config),
            '--challenge-from-export', str(exported['challenge']), '--solution-from-export', str(exported['solution']),
            '--inadvisably-no-sandbox'], timeout_seconds=args.kernel_timeout_seconds):
        return 1
    nanoda = {'use_stdin': False, 'export_file_path': str(exported['solution']),
              'permitted_axioms': selected['permitted_axioms'], 'unpermitted_axiom_hard_error': False,
              'num_threads': 1, 'nat_extension': True, 'string_extension': True}
    nanoda_path = out / 'nanoda.json'
    atomic_json(nanoda_path, nanoda)
    if not run('nanoda-one-thread', [str(prefix/'bin/nanoda_bin'), str(nanoda_path)],
               timeout_seconds=args.kernel_timeout_seconds):
        return 1
    if sha(config_path) != config_hash or any(sha(inventory[n]) != digest for n,digest in evidence['source_sha256'].items()):
        raise RuntimeError('Source or configuration changed during diagnostics')
    if runtime_artifacts(Path(cfg['lean'])) != evidence['runtime_artifacts']:
        raise RuntimeError('Compiler runtime changed during diagnostics')
    if any(sha(prefix/'bin'/n) != digest for n,digest in report['tool_sha256'].items()):
        raise RuntimeError('Diagnostic tool binary changed during checking')
    if any(sha(Path(__file__).with_name(n)) != digest for n,digest in report['driver_sha256'].items()):
        raise RuntimeError('Diagnostic driver or guard changed during checking')
    for kind, path in exported.items():
        if sha(path) != report[kind + '_export']['sha256']:
            raise RuntimeError('Proof export changed during checking')
    report['status'] = 'PASS_LOCAL_UNSANDBOXED_DIAGNOSTIC'
    report['finished_utc'] = datetime.now(timezone.utc).isoformat()
    atomic_json(report_path, report)
    print('PASS: local statement comparison, axiom restriction, Lean replay, and single-thread NanoDa replay.')
    print('UNSANDBOXED DIAGNOSTIC ONLY: full protected Palomar workflow remains unrun.')
    print('Receipt: ' + str(report_path))
    return 0


if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == '--export-worker':
        export_worker(sys.argv[2], sys.argv[3:])
    else:
        try:
            result_code = main()
        except BaseException as error:
            if ACTIVE_REPORT is not None:
                report_path, report = ACTIVE_REPORT
                if report.get('status') == 'RUNNING':
                    report.update(status='INCOMPLETE', error=str(error),
                                  finished_utc=datetime.now(timezone.utc).isoformat())
                    atomic_json(report_path, report)
            raise
        raise SystemExit(result_code)
