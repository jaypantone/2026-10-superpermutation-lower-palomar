"""Export the candidate and run the public judge's comparison/axiom/type checks.

Uses only the existing pinned compiler/cache and a separately downloaded public
judge package. Does not submit, run the Linux sandbox, or replay either kernel.
Run check.py for AlmanacAxioms and AlmanacChallenge first. Outputs stay in the
project's external shared workspace; only a small receipt is written in-repo.
"""
import argparse
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import shutil
import sys

from resource_guard import serialized, run_checked
from shared_setup import ROOT, layout, runtime_config, sha
from local_compare import checked_objects


@serialized
def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--judge-source", type=Path, required=True)
    parser.add_argument("--mode", choices=["fixed", "own"], required=True)
    args = parser.parse_args()
    loc, cfg = layout(), runtime_config()
    evidence, _ = checked_objects(loc, cfg, ["AlmanacSolution", "AlmanacChallenge"],
                                  ["almanac-preparation.json", "almanac-challenge.json"])
    out = loc["workspace"] / "verification/almanac-preflight"
    out.mkdir(parents=True, exist_ok=True)
    lib = out / "lib"
    (lib / "AlmanacJudge").mkdir(parents=True, exist_ok=True)
    judge = args.judge_source.resolve() / "judge"
    version = next(v for v in json.loads((judge / "versions.json").read_text())["versions"]
                   if v["lean"] == "v4.35.0")
    prefix = Path(cfg["lean"]).parent.parent
    env = dict(os.environ, LEAN_PATH=os.pathsep.join(
        [str(lib), str(loc["build"] / "lib")] + cfg["external_lean_paths"]),
        PATH=str(prefix / "bin") + os.pathsep + os.environ.get("PATH", ""),
        ELAN_TOOLCHAIN="leanprover/lean4:v4.35.0", LEAN_NUM_THREADS="1",
        OMP_NUM_THREADS="1", OPENBLAS_NUM_THREADS="1")
    report = {"status": "RUNNING", "started_utc": datetime.now(timezone.utc).isoformat(),
              "mode": args.mode, "steps": [],
              "scope": "Local public-judge comparison, axiom audit and statement extraction; neither kernel replay nor Linux sandbox verification.",
              "compiler_sha256": evidence["compiler_sha256"],
              "source_sha256": evidence["source_sha256"],
              "judge_source_sha256": {}}
    receipt = ROOT / "verification/almanac/preflight.json"

    def run(label, command):
        result = run_checked(command, cwd=out, env=env, log_path=out / (label + ".log"))
        report["steps"].append({"step": label, "exit_code": result.returncode,
                                "log_sha256": sha(out / (label + ".log")),
                                "resource_guard": result.resource_report})
        if result.returncode:
            report["status"] = "INCOMPLETE"
            receipt.write_text(json.dumps(report, indent=2) + "\n")
            print(result.stdout[-5000:])
            raise RuntimeError(f"Preflight stopped at {label}; no submission was made")
        print(label + ": passed", flush=True)

    for name in ["ToolchainCompat", "AlmanacJudge/Certs", "AlmanacJudge/Statement"]:
        source = judge / ("tools/v4.35.0" if name == "ToolchainCompat" else "tools/src") / (name + ".lean")
        dest = out / (name + ".lean")
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, dest)
        report["judge_source_sha256"][name] = sha(source)
        run("compile-" + name.replace("/", "-"), [cfg["lean"], "-j1", "-M4096",
            "-o", str(lib / (name + ".olean")), name + ".lean"])
    primitives = version["kernel_constants"]
    (out / "kernel-constants.txt").write_text("\n".join(primitives) + "\n")
    targets = list(dict.fromkeys(["almanac_claim", "propext", "Classical.choice", "Quot.sound"] + primitives))
    for kind, module in [("challenge", "AlmanacChallenge"), ("solution", "AlmanacSolution")]:
        destination = out / (kind + ".ndjson")
        destination.unlink(missing_ok=True)
        run("export-" + kind, [sys.executable, "-B", str(ROOT / "tools/local_compare.py"),
            "--export-worker", str(destination), str(prefix / "bin/leanexport"), module, "--", *targets])
        report[kind + "_export"] = {"bytes": destination.stat().st_size, "sha256": sha(destination)}
    source = judge / "tools/src/CompareMain.lean"
    shutil.copy2(source, out / "CompareMain.lean")
    report["judge_source_sha256"]["CompareMain"] = sha(source)
    run("compare", [cfg["lean"], "-j1", "-M4096", "--run", "CompareMain.lean",
                    "challenge.ndjson", "solution.ndjson", "almanac_claim",
                    "kernel-constants.txt", "comparison.json", args.mode])
    result = json.loads((out / "comparison.json").read_text())
    statement = result.pop("statement", None)
    report["comparison"] = result
    if statement is not None:
        text = json.dumps(statement, separators=(",", ":"), ensure_ascii=False)
        report["statement"] = {"complete": statement.get("complete"),
            "bytes": len(text.encode()), "declarations": len(statement.get("declarations", [])),
            "expressions": len(statement.get("expressions", [])), "error": statement.get("error")}
    ok = (result.get("compare", {}).get("ok") and result.get("axioms", {}).get("ok")
          and not result.get("axioms", {}).get("certificates")
          and not result.get("kernel_constants", {}).get("missing_in_challenge"))
    report["status"] = "PASS_LOCAL_COMPARISON" if ok else "FAILED"
    if args.mode == "own" and not (statement or {}).get("complete"):
        report["status"] = "INCOMPLETE_STATEMENT"
    report["finished_utc"] = datetime.now(timezone.utc).isoformat()
    receipt.write_text(json.dumps(report, indent=2) + "\n")
    print(report["status"], report.get("statement", "fixed statement"), flush=True)
    return 0 if report["status"] == "PASS_LOCAL_COMPARISON" else 1


if __name__ == "__main__":
    raise SystemExit(main())
