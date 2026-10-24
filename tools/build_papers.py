#!/usr/bin/env python3
"""Rebuild the lower-bound PDFs, keeping all intermediate files in a temporary directory."""
from pathlib import Path
import argparse
import os
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PAPERS = {'lower': 'lower-bounds', 'finite': 'finite-lower-bounds'}

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('papers', nargs='*', choices=list(PAPERS), help='Default: both lower-bound papers')
    parser.add_argument('--engine', choices=['tectonic', 'pdflatex'], help='Default: first installed engine')
    args = parser.parse_args()
    engine = args.engine or next((p for p in ('tectonic', 'pdflatex') if shutil.which(p)), None)
    if engine is None or shutil.which(engine) is None:
        parser.error('Install Tectonic or a TeX distribution providing pdflatex, then put it on PATH')
    for key in args.papers or PAPERS:
        folder = ROOT / 'papers' / key
        stem = PAPERS[key]
        with tempfile.TemporaryDirectory(prefix='superperm-paper-') as build_dir:
            build = Path(build_dir)
            if engine == 'tectonic':
                command = [engine, '--untrusted', '--outdir', str(build), str(folder / (stem + '.tex'))]
                subprocess.run(command, cwd=folder, check=True)
            else:
                command = [engine, '-no-shell-escape', '-halt-on-error', '-interaction=nonstopmode',
                           '-output-directory=' + str(build), str(folder / (stem + '.tex'))]
                for _ in range(2):
                    subprocess.run(command, cwd=folder, check=True)
            temporary = folder / (stem + '.pdf.pending')
            shutil.copy2(build / (stem + '.pdf'), temporary)
            os.replace(temporary, folder / (stem + '.pdf'))
            print('Built', folder / (stem + '.pdf'), flush=True)

if __name__ == '__main__':
    main()
