"""Source graphs and cache identities, shared by relocation and checking."""
from pathlib import Path
import hashlib
import json
import re
from shared_setup import ROOT, PROOFS, sha

OBJECT_SUFFIXES = ('.olean', '.olean.server', '.olean.private', '.ir', '.ilean')


def source_relative(path):
    return path.relative_to(PROOFS if path.is_relative_to(PROOFS) else ROOT)


def sources():
    """Collect source modules from root and the optional inherited proofs tree."""
    result = {}
    excluded = {'.git', '.lake', '__pycache__', 'node_modules', 'docbuild'}
    paths = sorted(p for p in ROOT.rglob('*.lean')
                   if not any(x in excluded for x in p.relative_to(ROOT).parts))
    for path in paths:
        name = '.'.join(source_relative(path).with_suffix('').parts)
        if name in result:
            raise RuntimeError('Duplicate Lean module: ' + name)
        result[name] = path
    return result


def imports(text):
    return [name for line in re.findall(r'^\s*(?:public\s+)?import\s+([^\n]+)',
                                       text, re.M)
            for name in line.split('--', 1)[0].split()]


def graph(targets, inventory):
    order, active, done, deps = [], set(), set(), {}
    def visit(name):
        if name in done:
            return
        if name in active:
            raise RuntimeError('Local import cycle: ' + name)
        if name not in inventory:
            raise RuntimeError('Unknown local target: ' + name)
        active.add(name)
        deps[name] = [d for d in imports(inventory[name].read_text()) if d in inventory]
        for dep in deps[name]:
            visit(dep)
        active.remove(name)
        done.add(name)
        order.append(name)
    for target in targets:
        visit(target)
    return order, deps


def keys(order, deps, inventory, compiler_sha256, external_paths):
    frozen = {name: sha(inventory[name]) for name in order}
    result = {}
    for name in order:
        # Byte-for-byte original build-key scheme enables independently checked
        # relocation of already compiled proofs without trusting path names.
        result[name] = hashlib.sha256(json.dumps([compiler_sha256, frozen[name],
            [result[d] for d in deps[name]], external_paths]).encode()).hexdigest()
    return frozen, result


def object_path(lib, module):
    return Path(lib).joinpath(*module.split('.')).with_suffix('.olean')


def artifacts(obj):
    if not obj.is_file():
        raise RuntimeError('Missing Lean object: ' + str(obj))
    return {suffix: sha(obj.with_suffix(suffix)) for suffix in OBJECT_SUFFIXES
            if obj.with_suffix(suffix).is_file()}


def runtime_artifacts(lean):
    toolchain = Path(lean).parent.parent
    paths = sorted((toolchain/'lib/lean').glob('*.dylib'))
    if not paths:
        paths = sorted((toolchain/'lib/lean').glob('*.so'))
    if not paths:
        raise RuntimeError('Cannot identify Lean implementation libraries')
    return {str(p.relative_to(toolchain)): sha(p) for p in paths}


def atomic_json(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(path.suffix + '.tmp')
    tmp.write_text(json.dumps(value, indent=2)+'\n')
    tmp.replace(path)
