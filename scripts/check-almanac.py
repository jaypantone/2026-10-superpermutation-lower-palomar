#!/usr/bin/env python3
"""Run the current public batch validator and repository rules on this candidate.

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
import tomllib

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
    from lean.batch import validate, challenge

    upstream = json.loads(args.mathlib_manifest.read_text())
    ecosystem = {p["name"]: p for p in upstream["packages"]}
    ecosystem["mathlib"] = {
        "url": "https://github.com/leanprover-community/mathlib4",
        "rev": PIN, "subDir": None, "configFile": "lakefile.lean",
        "manifestFile": "lake-manifest.json",
    }
    # Lake compares URLs literally when deciding whether to replace a checkout.
    # The older public static rules normalize .git, which misses this build failure.
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        expected = ecosystem.get(package["name"])
        if expected and (package["url"], package["rev"]) != (expected["url"], expected["rev"]):
            raise RuntimeError("Exact Mathlib URL/revision mismatch in lake-manifest.json: " + package["name"])
    config = tomllib.loads((ROOT / "lakefile.toml").read_text())
    for package in config.get("require", []):
        expected = ecosystem.get(package["name"])
        if expected and (package.get("git"), package.get("rev")) != (expected["url"], expected["rev"]):
            raise RuntimeError("Exact Mathlib URL/revision mismatch in lakefile.toml: " + package["name"])
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
        unchecked = []
        batch = validate.report(*validate.check(staged, unchecked), unchecked, validate.paper(staged))
        if not batch["ok"] or unchecked:
            raise RuntimeError("Batch validation failed: " + json.dumps(batch))
        trusted = challenge.build_files()
        for name, expected in trusted.items():
            if (staged / name).read_text() != expected["text"]:
                raise RuntimeError("Local judge file differs from the public judge: " + name)
        for paper in (staged / "paper").rglob("*"):
            if paper.is_file():
                original = staged / "papers" / paper.relative_to(staged / "paper")
                if not original.is_file() or sha(paper) != sha(original):
                    raise RuntimeError("Paper copy differs from its source: " + str(paper))
        result = check_all(staged, {}, toolchain="leanprover/lean4:v4.35.0",
                           dependencies={}, ecosystem=ecosystem, entry_at_root=True)
    record = {
        "status": "PASS_BATCH_AND_REPOSITORY_RULES",
        "batch": batch,
        "recorded_utc": datetime.now(timezone.utc).isoformat(),
        "scope": "Official batch parser, layout, manifest, source and paper checks; no hosted preview, submission, Lean replay, or NanoDa replay.",
        "judge_source_url": "https://web-production-daed9.up.railway.app/lean/judge-source.tar.gz",
        "judge_source_sha256": {name: sha(args.judge_source / name) for name in
            ["judge/stages/rules.py", "judge/versions.json", "lean/batch/validate.py",
             "lean/batch/registry.py", "lean/batch/entry.py", "lean/batch/challenge.py", "lean/batch/paper.py"]},
        "mathlib_commit": PIN,
        "exact_mathlib_urls_and_revisions": "PASS",
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
    print(json.dumps({
        "status": record["status"],
        "wrappers": [{"name": w["name"], "classification": w["classification"],
                      "template": w["template"]} for w in batch["wrappers"]],
        "problems": batch["problems"], "catalogue_sha256": batch["catalogue_sha256"],
        "paper_files": (batch.get("paper") or {}).get("count", 0),
        "ignored_paper_files": (batch.get("paper") or {}).get("ignored_count", 0),
        "files": len(names), "bytes": total, "lean_files": result.lean_files,
        "source_scan_counts": record["source_scan_counts"], "scope": record["scope"],
    }, indent=2))


if __name__ == "__main__":
    main()
