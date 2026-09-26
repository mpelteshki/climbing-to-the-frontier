# P3 C5: selected finite sizes

[Cell statement](https://hackathon.bainsa.ai/p/p3/c5) · [Package and replay instructions](../README.md)

Theorems `maximumDepth_3`, `maximumDepth_5`, `maximumDepth_8`, `maximumDepth_12`, `maximumDepth_17`, and `maximumDepth_23` prove exact maximum first-periodic depths 2, 3, 5, 8, 12, and 18, respectively, over **all** partitions of each size. These are finite instances, not a general C5 theorem. C5 remains partial.

## General lower bound

The [explicit written witness proof](lower-bound-proof.md) establishes depth `(k−1)(k−4)` for its displayed family for every k≥5. Its full modular trajectory is proved, with a separate direct sanity check through k=50. The witness is not optimal at k=5,6. C5 remains **Not solved**: a matching uniform upper bound for k≥7 and the requested comparison with the C3 method remain outstanding.
