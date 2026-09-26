#!/usr/bin/env python3
"""Sequential full rerun of the two P4 searches and saved certificate checks."""
import json
import argparse
from pathlib import Path
import subprocess
import sys
import tempfile
from time import monotonic

from audit import valid_residues

ROOT = Path(__file__).resolve().parent


def load(name):
    return [json.loads(line) for line in (ROOT / name).read_text().splitlines()]


def run(argv, timeout):
    start = monotonic()
    process = subprocess.run([sys.executable, "-B", *argv], cwd=ROOT,
                             capture_output=True, text=True, timeout=timeout, check=True)
    return process.stdout, round(monotonic() - start, 3)


def nodes(row):
    return sum(n for key, n in row["counts"].items()
               if key.startswith("node_") or key.endswith("_nodes"))


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-k", type=int, choices=(14, 16), default=16)
    parser.add_argument("--output-dir", type=Path,
                        help="fresh directory for outputs (default: new temporary directory)")
    args = parser.parse_args()
    maximum = args.max_k
    output_dir = args.output_dir or Path(tempfile.mkdtemp(prefix="p4-replay-"))
    output_dir.mkdir(parents=True, exist_ok=True)
    TUPLE = output_dir / f"rerun-tuple-9-{maximum}.jsonl"
    CLIQUE = output_dir / f"rerun-clique-9-{maximum}.jsonl"
    STRONG = output_dir / "rerun-rule-on-9-14.jsonl"
    POSITIVE = output_dir / f"rerun-positive-control-9-{maximum}.jsonl"
    EVIDENCE = output_dir / f"replay-evidence-9-{maximum}.json"
    def save(evidence):
        EVIDENCE.write_text(json.dumps(evidence, indent=2, sort_keys=True) + "\n")
    tuple_base = {row["k"]: row for name in
        ("run-9-14.jsonl", "run-15-strong-60.jsonl", "run-16-strong-300.jsonl")
        for row in load(name)}
    clique_base = {row["k"]: row for name in
        ("clique-9-12.jsonl", "clique-13-14.jsonl",
         "clique-15-strong.jsonl", "clique-16-strong.jsonl")
        for row in load(name)}
    assert set(tuple_base) == set(clique_base) == set(range(9, 17))
    for path in (TUPLE, CLIQUE, STRONG, POSITIVE, EVIDENCE):
        assert not path.exists(), "refusing to overwrite " + str(path)
    start = monotonic()
    evidence = {
        "complete": False, "sizes": [], "checks": {}, "rule_on_off": [],
        "output_dir": str(output_dir),
        "shared_validator": "clique.py imports audit.maximal_power_failure for its leaf rule; graph/multiplicity enumeration is independent",
        "residue_checker_correction": "audit.py now compares xs[j] == xs[i] for original equal moduli, not xs[j] == R_i; fresh global-minimum claims and all 20436 fact statuses and witnesses matched saved data exactly",
    }
    save(evidence)
    try:
        with TUPLE.open("x") as tuple_file, CLIQUE.open("x") as clique_file:
            for k in range(9, maximum + 1):
                strong = k >= 15
                seconds = 300 if strong else 60
                detail = {}
                results = {}
                for script, baseline, stream in (
                    ("enumerate.py", tuple_base[k], tuple_file),
                    ("clique.py", clique_base[k], clique_file),
                ):
                    argv = [script, str(k), "--seconds", str(seconds)]
                    if strong:
                        argv.append("--strong")
                    output, wall = run(argv, seconds + 30)
                    lines = output.splitlines()
                    assert len(lines) == 1
                    result = json.loads(lines[0])
                    assert result["k"] == k and result["complete"] is True
                    for field in ("domain_size", "counts", "base_survivors",
                                  "reduced_survivors"):
                        assert result[field] == baseline[field], (script, k, field)
                    if script == "enumerate.py":
                        assert result["anchor_count"] == baseline["anchor_count"]
                    stream.write(json.dumps(result, sort_keys=True) + "\n")
                    stream.flush()
                    results[script] = result
                    detail[script] = {
                        "wall_seconds": wall,
                        "reported_seconds": result["seconds"],
                        "nodes": nodes(result),
                        "baseline_nodes": nodes(baseline),
                        "base_survivors": len(result["base_survivors"]),
                        "reduced_survivors": len(result["reduced_survivors"]),
                        "exact_baseline_match": True,
                    }
                    print(json.dumps({"k": k, "script": script, **detail[script]}), flush=True)
                field = "base_survivors" if k <= 14 else "reduced_survivors"
                assert results["enumerate.py"][field] == results["clique.py"][field]
                evidence["sizes"].append({
                    "k": k, "compared_field": field,
                    "independent_lists_equal": True, **detail,
                })
                evidence["overall_wall_seconds"] = round(monotonic() - start, 3)
                save(evidence)

        # Switch all three optional early feasibility rules on, then compare
        # with the independently reproduced rule-off run above. The complete
        # tuple leaf test stays the same in both runs.
        with STRONG.open("x") as strong_file:
            for k in range(9, 15):
                baseline = tuple_base[k]
                output, wall = run(["enumerate.py", str(k), "--seconds", "60", "--strong"], 90)
                result = json.loads(output)
                assert result["complete"] is True and result["strong_pruning"] is True
                assert result["reduced_survivors"] == baseline["reduced_survivors"]
                strong_file.write(json.dumps(result, sort_keys=True) + "\n")
                strong_file.flush()
                evidence["rule_on_off"].append({
                    "k": k, "rule_off_baseline_complete": True,
                    "rule_on_complete": True, "same_reduced_survivors": True,
                    "rule_on_wall_seconds": wall,
                    "rule_on_nodes": nodes(result),
                    "rule_off_nodes": nodes(baseline),
                })
                save(evidence)

        output, wall = run(["enumerate.py", "7", "--target-length", "6",
                            "--seconds", "60"], 90)
        positive = json.loads(output)
        baseline = load("positive-control.jsonl")[0]
        for field in ("counts", "base_survivors", "reduced_survivors", "domain_size"):
            assert positive[field] == baseline[field]
        six = [6] * 6
        assert six in positive["base_survivors"]
        assert valid_residues(six, list(range(6)))
        POSITIVE.write_text(json.dumps(positive, sort_keys=True) + "\n")
        evidence["checks"]["positive_control"] = {
            "complete": True, "wall_seconds": wall,
            "moduli": six, "residues": list(range(6)),
        }
        save(evidence)

        checks = (
            ("audit_9_14", ["audit.py", "run-9-14.jsonl"]),
            ("independent_comparison", ["compare_independent.py", "--tuple-runs",
                str(TUPLE), "--clique-runs", str(CLIQUE)]),
            ("global_minima", ["verify_global_minima.py", "--runs",
                "run-15-strong-60.jsonl", "run-16-strong-300.jsonl",
                "--facts", "global-minima-facts.jsonl",
                "--claims", "global-minima-claims.jsonl"]),
            ("refutation_trees", ["verify_refutations.py",
                "global-minima-claims.jsonl", "minimum-refutations.jsonl"]),
            ("compact_trees", ["verify_cert_strings.py",
                "minimum-refutations.jsonl", "cert-strings.json"]),
        )
        for name, argv in checks:
            output, wall = run(argv, 60)
            if name == "audit_9_14":
                assert json.loads(output) == json.loads((ROOT / "rerun-audit-9-14.json").read_text())
                detail = {"exact_corrected_output_match": True}
            elif name == "independent_comparison":
                comparison = [json.loads(line) for line in output.splitlines()]
                assert len(comparison) == maximum - 8
                assert all(not row["tuple_only"] and not row["clique_only"]
                           for row in comparison)
                detail = {"sizes": maximum - 8, "all_symmetric_differences_empty": True}
            else:
                detail = json.loads(output)
                assert detail["complete"] is True
            evidence["checks"][name] = {"wall_seconds": wall, **detail}
            save(evidence)
        evidence["complete"] = True
        evidence["overall_wall_seconds"] = round(monotonic() - start, 3)
        save(evidence)
        print(json.dumps({"complete": True,
                          "overall_wall_seconds": evidence["overall_wall_seconds"]}), flush=True)
    except BaseException as error:
        evidence["failure"] = repr(error)
        evidence["overall_wall_seconds"] = round(monotonic() - start, 3)
        save(evidence)
        raise


if __name__ == "__main__":
    main()
