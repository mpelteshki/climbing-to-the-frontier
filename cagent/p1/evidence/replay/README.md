# Fresh local replay

From the existing isolated Lean 4.34.1 project with Mathlib at `d13f23b723b8a846827a245b89c10fc7d3f11612`, run:

```sh
cd /Users/martin/Documents/LW/proof-pursuit-p1/increments/c4-geometric-core/cagent/p1
./evidence/replay-local.sh
```

The script uses `lake env`, creates a fresh directory under `/private/tmp`, removes the isolated project's previous `.lake/build/lib/lean` from `LEAN_PATH`, prepends the fresh directory, and compiles each source with `lean -o` in dependency order. Its run exited 0. [output-dir.txt](output-dir.txt) records the particular output directory. Each log below is the exact output of compiling the packaged source; [source-sha256.txt](../source-sha256.txt) records source hashes. A clean network download was not part of this replay; the package's portable [verify.sh](../../verify.sh) specifies that path.

| Module | Printed declarations |
| --- | ---: |
| [Angles](Angles.log) | 6 |
| [C4Pentagon](C4Pentagon.log) | 6 |
| [C4Extremum](C4Extremum.log) | 2 |
| [C4Rotation](C4Rotation.log) | 1 |
| [C4SparseStep](C4SparseStep.log) | 4 |
| [C4SignedSparse](C4SignedSparse.log) | 1 |
| [C4Geometry](C4Geometry.log) | 4 |
| [C4LocalRotation](C4LocalRotation.log) | 1 |
| [C4Selection](C4Selection.log) | 1 |
| [C4Configuration](C4Configuration.log) | 3 |
| [C4Replacement](C4Replacement.log) | 8 |
| [C4Direction](C4Direction.log) | 1 |
| [C4MaximalSparse](C4MaximalSparse.log) | 2 |
| [C4NeighborCount](C4NeighborCount.log) | 2 |
| [C4SparseConfiguration](C4SparseConfiguration.log) | 2 |
| [C4MatrixCorank](C4MatrixCorank.log) | 5 |
| [C4FiveCycle](C4FiveCycle.log) | 1 |
| [C4SixCycle](C4SixCycle.log) | 1 |

All 51 printed declarations list exactly `propext`, `Classical.choice`, and `Quot.sound`. No replay log reports a compiler error. The source contains no `sorry`, `admit`, custom `axiom`, `unsafe`, or `native_decide` escape hatch.
