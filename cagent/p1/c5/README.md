# C5: d + 2 lines

**Status: Solved — complete written proof; Lean partial.** The [complete proof](proof.md) establishes the requested sharp bound for every d ≥ 2 and N = d + 2, including repeated lines. It extends the C4 sparse-graph and projection argument with a scalar monotonicity step. Its hypotheses and component accounting were independently audited.

The full general C5 statement is not formalized in Lean. `Angles.c5_d2` in [Angles.lean](../Angles.lean) proves the d = 2 case for arbitrary planar unit representatives. The C4 Lean modules verify the equality-case local projection inequality, sparse maximizer, and ordered-band matrix corank lemmas used in the written argument; the general monotonicity extension and final induction remain written only. [Replay evidence](../evidence/replay/README.md) checks the Lean source.

The [literature note](literature.md) records primary sources and provenance. The projection proof was reconstructed in this work; no novelty or organizer acceptance is claimed. The original 1959 paper's full proof was not inspected and is not used as a substitute for the proof here.
