#!/usr/bin/env python3
"""Rebuild and replay C5 k=15/16 early-rule ablation, then check certificates."""

import argparse
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile
from time import monotonic

ROOT = Path(__file__).resolve().parent
SOURCE = ROOT / "rule_ablation.cpp"


def run(command, timeout, cwd=ROOT):
    started = monotonic()
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True,
                            check=True, timeout=timeout)
    return result.stdout, round(monotonic() - started, 3)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output-dir", type=Path)
    args = parser.parse_args()
    out = args.output_dir or Path(tempfile.mkdtemp(prefix="p4-c5-ablation-"))
    out.mkdir(parents=True, exist_ok=True)
    binary = out / "rule_ablation"
    evidence_path = out / "ablation-evidence.json"
    for path in (binary, evidence_path):
        if path.exists():
            raise FileExistsError(path)

    started = monotonic()
    _, build_seconds = run(["c++", "-std=c++17", "-O3", "-Wall", "-Wextra",
                            "-pedantic", str(SOURCE), "-o", str(binary)], 60)
    evidence = {"complete": False,
                "source_sha256": hashlib.sha256(SOURCE.read_bytes()).hexdigest(),
                "build_seconds": build_seconds, "sizes": [], "certificate_checks": {}}
    evidence_path.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    for k, file in ((15, "run-15-strong-60.jsonl"),
                    (16, "run-16-strong-300.jsonl")):
        baseline = json.loads((ROOT / file).read_text())
        results = {}
        for mode in ("on", "off"):
            raw, wall = run([str(binary), str(k), mode], 580)
            result = json.loads(raw)
            assert result["k"] == k and result["strong"] is (mode == "on")
            assert result["domain_size"] == baseline["domain_size"]
            assert result["anchor_count"] == baseline["anchor_count"]
            assert result["anchor_triples"] == baseline["counts"]["anchor_triples"]
            assert result["survivors"] == baseline["reduced_survivors"]
            result["command_wall_seconds"] = wall
            (out / f"{mode}-{k}.json").write_text(
                json.dumps(result, indent=2, sort_keys=True) + "\n")
            results[mode] = result
        assert results["on"]["survivors"] == results["off"]["survivors"]
        evidence["sizes"].append({
            "k": k, "survivors": len(results["on"]["survivors"]),
            "exact_lists_equal": True,
            "each_equals_independently_checked_baseline": True,
            "on_nodes": sum(results["on"]["nodes_by_depth"]),
            "off_nodes": sum(results["off"]["nodes_by_depth"]),
            "on_wall_seconds": results["on"]["command_wall_seconds"],
            "off_wall_seconds": results["off"]["command_wall_seconds"],
        })
        evidence["overall_wall_seconds"] = round(monotonic() - started, 3)
        evidence_path.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")

    checks = {
        "minimum_cardinality": ["python3", "-B", "verify_global_minima.py",
            "--runs", "run-15-strong-60.jsonl", "run-16-strong-300.jsonl",
            "--facts", "global-minima-facts.jsonl",
            "--claims", "global-minima-claims.jsonl"],
        "refutation_trees": ["python3", "-B", "verify_refutations.py",
            "global-minima-claims.jsonl", "minimum-refutations.jsonl"],
        "compact_trees": ["python3", "-B", "verify_cert_strings.py",
            "minimum-refutations.jsonl", "cert-strings.json"],
    }
    for name, command in checks.items():
        raw, wall = run(command, 60)
        detail = json.loads(raw)
        assert detail["complete"] is True
        evidence["certificate_checks"][name] = {**detail, "wall_seconds": wall}
    evidence["overall_wall_seconds"] = round(monotonic() - started, 3)
    evidence["complete"] = True
    evidence_path.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    print(json.dumps(evidence, sort_keys=True))


if __name__ == "__main__":
    main()
