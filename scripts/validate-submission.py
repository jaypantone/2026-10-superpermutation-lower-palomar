#!/usr/bin/env python3
"""Run pinned Palomar metadata/config checks; no build, upload, or submission.

Supply an unmodified checkout of the recorded PalomarSubmission revision.
Requires PyYAML. This is a limited static check, not full Palomar preflight.
"""
import argparse
import json
import subprocess
import sys
import yaml
from pathlib import Path

PIN = 'ad5db9e7ff8b17523d73aeb244aaeabcde810c64'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--palomar-source', required=True, type=Path)
    args = parser.parse_args()
    source = args.palomar_source.resolve()
    actual = subprocess.check_output(['git', '-C', str(source), 'rev-parse', 'HEAD'], text=True).strip()
    if actual != PIN:
        parser.error(f'Palomar source must be at {PIN}; found {actual}')
    subprocess.run(['git', '-C', str(source), 'diff', '--quiet', 'HEAD'], check=True)
    root = Path(__file__).resolve().parents[1]
    sys.path.insert(0, str(source))
    from scripts.submission_contract import load_formalization_metadata
    from scripts.verify_submission import load_comparator_config
    subprocess.run([sys.executable, str(root / 'scripts/check-lean-sources.py')], check=True)
    load_formalization_metadata(root / 'formalization.yaml')
    # The current policy restricts source types; the pinned validator predates this rule.
    metadata = yaml.safe_load((root / 'formalization.yaml').read_text())
    source_types = {'paper', 'book', 'web discussion', 'folklore', 'original-proof', 'other'}
    for index, source in enumerate(metadata.get('sources', [])):
        if 'type' in source and source['type'] not in source_types:
            parser.error(f'Unsupported sources[{index}].type: {source["type"]}')
    reports = []
    for config_path in sorted(root.glob('comparator*.json')):
        cfg = load_comparator_config(config_path)
        challenge = root.joinpath(*cfg['challenge_module'].split('.')).with_suffix('.lean')
        solution = root.joinpath(*cfg['solution_module'].split('.')).with_suffix('.lean')
        for path in (challenge, solution):
            if path.is_symlink() or not path.is_file():
                parser.error(f'Missing regular module source: {path}')
        raw = challenge.read_bytes()
        lines = raw.count(b'\n') + int(bool(raw) and not raw.endswith(b'\n'))
        if len(raw) > 100 * 1024 or lines > 1000:
            parser.error(f'Challenge exceeds hard cap: {challenge}')
        reports.append({'configuration': config_path.name, 'theorems': len(cfg['theorem_names']),
                        'challenge_bytes': len(raw), 'challenge_lines': lines})
    if not reports:
        parser.error('No comparator*.json configurations found')
    print(json.dumps({'static_checks': 'passed', 'palomar_revision': PIN,
                      'configurations': reports,
                      'limitation': 'No Lean build, Comparator, independent kernel, licence detector, or full Palomar workflow ran.'}, indent=2))


if __name__ == '__main__':
    main()
