"""Resolve existing pinned shared tooling; stage sources outside Dropbox.

This tool never installs or downloads anything and never changes dependencies.
Run prepare_workspace only under this repository's compiler lock.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import tomllib

ROOT = Path(__file__).resolve().parents[1]
PROOFS = ROOT / 'proofs'
ENVIRONMENT = ROOT
MIN_FREE_BYTES = 15 * 1024**3


def sha(path):
    h = hashlib.sha256()
    with Path(path).open('rb') as f:
        for b in iter(lambda: f.read(8 * 1024 * 1024), b''):
            h.update(b)
    return h.hexdigest()


def external_path(path):
    path = Path(path).expanduser()
    if not path.is_absolute():
        raise RuntimeError('Shared Lean locations must be absolute')
    path = path.resolve()
    if 'Dropbox' in path.parts or path.is_relative_to(ROOT):
        raise RuntimeError('Shared Lean files must stay outside Dropbox and this repository')
    return path


def layout():
    shared = external_path(os.environ.get('SUPERPERM_LEAN_CACHE',
        os.environ.get('LEAN_SHARED_CACHE', '~/Library/Caches/LeanShared')))
    elan = external_path(os.environ.get('ELAN_HOME', '~/.elan'))
    toolchain = (ENVIRONMENT/'lean-toolchain').read_text().strip()
    config = tomllib.loads((ENVIRONMENT/'lakefile.toml').read_text())
    # Keep the existing expanded cache identity after correcting the public
    # Lake URL spelling. This is only a local storage key, never a Lake URL.
    requirements = [dict(r) for r in config.get('require', [])]
    for requirement in requirements:
        if (requirement.get('name') == 'mathlib' and
            requirement.get('git') == 'https://github.com/leanprover-community/mathlib4'):
            requirement['git'] += '.git'
    spec = {'toolchain': toolchain, 'require': requirements}
    dependency_id = hashlib.sha256(json.dumps(spec, sort_keys=True).encode()).hexdigest()
    workspace_id = hashlib.sha256(str(ROOT).encode()).hexdigest()[:16]
    dependency = shared/'dependencies'/dependency_id
    workspace = shared/'workspaces'/workspace_id/dependency_id
    toolchain_dir = elan/'toolchains'/toolchain.replace('/', '--').replace(':', '---')
    return {'shared': shared, 'elan': elan, 'toolchain': toolchain_dir,
            'dependency': dependency, 'packages': dependency/'packages',
            'workspace': workspace, 'sources': workspace/'sources',
            'build': workspace/'build', 'dependency_id': dependency_id,
            'workspace_id': workspace_id}


def require_free_disk(path):
    path = Path(path)
    while not path.exists():
        path = path.parent
    free = shutil.disk_usage(path).free
    if free < MIN_FREE_BYTES:
        raise RuntimeError('Stopped: fewer than 15 GiB of free disk space remain')
    return free


def runtime_config():
    loc = layout()
    manifest = json.loads((ENVIRONMENT/'lake-manifest.json').read_text())
    package_names = {p['name'] for p in manifest['packages']}
    preferred = ['mathlib', 'plausible', 'proofwidgets', 'batteries', 'aesop',
                 'importGraph', 'LeanSearchClient', 'Qq']
    names = [n for n in preferred if n in package_names]
    # Some optional tool-only packages (for example Cli) have no objects in
    # a minimal mathematical dependency cache. Include their paths only when
    # objects exist; requested imports still fail normally if absent.
    names += [n for n in sorted(package_names - set(names))
              if (loc['packages']/n/'.lake/build/lib/lean').is_dir()]
    if len(set(names)) != len(names) or any('/' in n or n in {'.', '..'} for n in names):
        raise RuntimeError('Invalid library path order')
    return {'lean': str(loc['toolchain']/'bin/lean'),
        'external_lean_paths': [str(loc['packages']/n/'.lake/build/lib/lean') for n in names],
        'output': str(loc['build']), 'threads': 1,
        'shared_cache': str(loc['shared']), 'workspace': str(loc['workspace']),
        'dependency_id': loc['dependency_id']}


def validate_dependencies():
    loc = layout()
    cfg = runtime_config()
    if not Path(cfg['lean']).is_file():
        raise RuntimeError('Pinned shared compiler is absent; no installation was attempted')
    manifest = json.loads((ENVIRONMENT/'lake-manifest.json').read_text())
    stored = json.loads((loc['dependency']/'lake-manifest.json').read_text())
    def key(data):
        packages = [dict(p) for p in data['packages']]
        # The fixed local cache predates the judge's URL spelling correction.
        # Compare every other field, including exact revisions, unchanged.
        for package in packages:
            if (package.get('name') == 'mathlib' and
                package.get('url') == 'https://github.com/leanprover-community/mathlib4.git'):
                package['url'] = 'https://github.com/leanprover-community/mathlib4'
        return sorted(packages, key=lambda p: p['name'])
    if key(stored) != key(manifest):
        raise RuntimeError('Shared dependency revisions differ; refusing in-place changes')
    for path in cfg['external_lean_paths']:
        if not Path(path).is_dir():
            raise RuntimeError('Missing expanded pinned dependency objects: ' + path)
    return loc


def prepare_workspace():
    loc = validate_dependencies()
    require_free_disk(loc['shared'])
    loc['sources'].mkdir(parents=True, exist_ok=True)
    link = loc['workspace']/'.lake/packages'
    link.parent.mkdir(parents=True, exist_ok=True)
    if link.is_symlink():
        if link.resolve() != loc['packages']:
            raise RuntimeError('Unexpected shared-package link')
    elif link.exists():
        raise RuntimeError('Refusing to replace a private dependency directory')
    else:
        link.symlink_to(loc['packages'], target_is_directory=True)
    records = {}
    from proof_sources import sources, source_relative
    for source in sources().values():
        relative = source_relative(source)
        destination = loc['sources']/relative
        data = source.read_bytes()
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists() or destination.read_bytes() != data:
            shutil.copy2(source, destination)
        records[str(relative)] = hashlib.sha256(data).hexdigest()
    (loc['workspace']/'staging.json').write_text(json.dumps({
        'source_project': str(ROOT), 'sha256': records,
        'lean_compilation_performed': False}, indent=2)+'\n')
    (loc['workspace']/'runtime.json').write_text(json.dumps(runtime_config(), indent=2)+'\n')
    return loc


def staged_root(source_root=PROOFS):
    if Path(source_root).resolve() not in {PROOFS.resolve(), ROOT.resolve()}:
        raise RuntimeError('Unexpected local source root')
    return layout()['sources']


if __name__ == '__main__':
    print(json.dumps({k: str(v) for k,v in layout().items()}, indent=2))
