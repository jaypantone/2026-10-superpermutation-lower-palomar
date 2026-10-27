#!/usr/bin/env python3
"""Run the public Almanac repository rules on a clean copy of this candidate.

Supply the unpacked /lean/judge-source.tar.gz and the upstream Mathlib manifest
downloaded at the pinned revision. This neither builds Lean nor submits a job.
Tracked and nonignored new files are checked; git metadata/build caches are not.
"""
import argparse
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
PIN = "56a005855ea17e0b0958f73ec801ae140b0a1679"


def sha(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--judge-source", type=Path, required=True)
    parser.add_argument("--mathlib-manifest", type=Path, required=True)
    parser.add_argument("--receipt", type=Path)
    args = parser.parse_args()
    sys.path.insert(0, str(args.judge_source.resolve()))
    from judge.stages.rules import check_all

    upstream = json.loads(args.mathlib_manifest.read_text())
    ecosystem = {p["name"]: p for p in upstream["packages"]}
    ecosystem["mathlib"] = {
        "url": "https://github.com/leanprover-community/mathlib4.git",
        "rev": PIN, "subDir": None, "configFile": "lakefile.lean",
        "manifestFile": "lake-manifest.json",
    }
    names = sorted(set(subprocess.check_output(
        ["git", "ls-files", "--cached", "--others", "--exclude-standard", "-z"],
        cwd=ROOT).decode().split("\0")) - {""})
    names = [n for n in names if (ROOT / n).exists() or (ROOT / n).is_symlink()]
    with tempfile.TemporaryDirectory(prefix="almanac-rules-") as tmp:
        staged = Path(tmp)
        total = 0
        for name in names:
            source, target = ROOT / name, staged / name
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target, follow_symlinks=False)
            total += source.lstat().st_size
        if total > 500 * 1024**2:
            raise RuntimeError("Candidate exceeds 500 MiB")
        result = check_all(staged, {}, toolchain="leanprover/lean4:v4.35.0",
                           dependencies={}, ecosystem=ecosystem)
    record = {
        "status": "PASS_STATIC_REPOSITORY_RULES",
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Public rules only; no submission, Lean replay, or NanoDa replay.",
        "judge_source_url": "https://web-production-daed9.up.railway.app/lean/judge-source.tar.gz",
        "rules_sha256": sha(args.judge_source / "judge/stages/rules.py"),
        "mathlib_commit": PIN,
        "upstream_mathlib_manifest_sha256": sha(args.mathlib_manifest),
        "files": len(names), "bytes": total,
        "lean_files": result.lean_files, "lean_lines": result.lean_lines,
        "layout_dir": result.layout_dir, "packages": result.packages,
        "source_scan_counts": dict(Counter(f["token"] for f in result.source_findings)),
        "source_scan_note": "Native-track restrictions are diagnostic here; these claims use only the three standard axioms. Independent Challenge placeholders are not imported by AlmanacSolution.",
        "input_sha256": {n: sha(ROOT / n) for n in names if n.endswith((".lean", ".toml")) or n in {"lean-toolchain", "lake-manifest.json"}},
    }
    if args.receipt:
        args.receipt.parent.mkdir(parents=True, exist_ok=True)
        args.receipt.write_text(json.dumps(record, indent=2) + "\n")
    print(json.dumps({k: v for k, v in record.items() if k != "input_sha256"}, indent=2))


if __name__ == "__main__":
    main()
