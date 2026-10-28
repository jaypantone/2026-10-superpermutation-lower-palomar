"""Conservative source hygiene for these standard-axiom submission candidates.

This is a useful preflight, not proof verification. Comparator's axiom check and
both kernel replays remain necessary. Challenge placeholders are permitted only
in challenge modules explicitly named by the repository's configurations.
"""
import json
import hashlib
import re
from shared_setup import ROOT


def code_only(text):
    """Remove Lean strings and nested/line comments, retaining line breaks."""
    result, pos, depth, string = [], 0, 0, False
    while pos < len(text):
        pair = text[pos:pos + 2]
        char = text[pos]
        if depth:
            if pair == '/-':
                depth += 1
                result.extend('  ')
                pos += 2
            elif pair == '-/':
                depth -= 1
                result.extend('  ')
                pos += 2
            else:
                result.append('\n' if char == '\n' else ' ')
                pos += 1
        elif string:
            if char == '\\':
                result.extend('  ')
                pos += 2
            else:
                if char == '"':
                    string = False
                result.append('\n' if char == '\n' else ' ')
                pos += 1
        elif pair == '/-':
            depth = 1
            result.extend('  ')
            pos += 2
        elif pair == '--':
            end = text.find('\n', pos)
            if end < 0:
                end = len(text)
            result.extend(' ' * (end - pos))
            pos = end
        elif char == '"':
            string = True
            result.append(' ')
            pos += 1
        else:
            result.append(char)
            pos += 1
    if depth or string:
        raise RuntimeError('Unterminated Lean block comment or string')
    return ''.join(result)


def validate_sources(inventory):
    configs = sorted(ROOT.glob('comparator*.json'))
    if not configs:
        raise RuntimeError('No Comparator configuration found')
    challenge_modules = set()
    for path in configs:
        cfg = json.loads(path.read_text())
        challenge_modules.add(cfg['challenge_module'])
        if cfg['solution_module'] == cfg['challenge_module']:
            raise RuntimeError('Challenge and solution environments must differ')
        if cfg.get('definition_names'):
            raise RuntimeError('This project submits theorem claims only')
        if set(cfg['permitted_axioms']) != {'propext', 'Quot.sound', 'Classical.choice'}:
            raise RuntimeError('Unexpected permitted axioms in ' + path.name)
        if cfg.get('enable_nanoda') is not True:
            raise RuntimeError('Independent kernel replay must remain enabled')
    if not challenge_modules <= set(inventory):
        raise RuntimeError('A configured challenge source is absent')
    # Public judge-owned templates are deliberately core Lean (no module header).
    # Accept only the exact downloaded bytes, including the challenge placeholder.
    almanac_templates = {'AlmanacDefs': '3e869f896a193e67da97c4fa535ddccec2e2f3d3152d2cbf552373159e138b0f', 'AlmanacStatement': 'c048c75c545218b82e86826ac7cdb2083ceea86583cc8db5bb0b0d36fc598800', 'AlmanacChallenge': '6676b64886e1d0215aa2ef2350f3320d5725479f5db8d5ca77f84a851531f09f'}
    for name, path in inventory.items():
        if name in almanac_templates:
            if hashlib.sha256(path.read_bytes()).hexdigest() != almanac_templates[name]:
                raise RuntimeError("Changed judge-owned template: " + name)
            continue
        text = path.read_text()
        code = code_only(text)
        if name not in {'AlmanacStatement', 'AlmanacAdapter', 'AlmanacSolution', 'AlmanacAxioms'} and not re.match(r'\s*module\b', code):
            raise RuntimeError('Missing module header: ' + name)
        if len(text.splitlines()) > 10000:
            raise RuntimeError('Source exceeds 10000 lines: ' + name)
        if re.search(r'\b(?:native_decide|axiom|unsafe)\b', code):
            raise RuntimeError('Forbidden native computation or declaration: ' + name)
        if re.search(r'\b(?:sorry|admit)\b', code) and name not in challenge_modules:
            raise RuntimeError('Proof placeholder outside an independent challenge: ' + name)
        if name in challenge_modules:
            if len(text.splitlines()) > 1000 or len(text.encode()) > 100 * 1024:
                raise RuntimeError('Challenge exceeds Palomar size limits: ' + name)
            from proof_sources import imports
            local = [x for x in imports(code) if x in inventory]
            if local:
                raise RuntimeError('Challenge imports project proofs: ' + name)
    return {'modules': len(inventory), 'challenges': sorted(challenge_modules)}


if __name__ == '__main__':
    from proof_sources import sources
    print(json.dumps(validate_sources(sources()), indent=2))
