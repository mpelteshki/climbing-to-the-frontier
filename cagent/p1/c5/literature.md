# C5 literature check and provenance (2026-09-26)

## Exact primary-source evidence

1. F. Fodor, V. Vígh, T. Zarnócz, *On the angle sum of lines*, Archiv der Mathematik 106 (2016), 91–100, [author-hosted preprint](https://www.math.u-szeged.hu/~vigvik/preprints/egyenesekszogei.pdf), introduction pp. 1–2. It defines (S(n,d)) for lines in (ℝ^d), states the repeated-coordinate-axis configuration as the conjectured optimum, and says Fejes Tóth stated the conjecture only for (d=3). It explicitly reports that he determined (S(n,3)) for (n≤5) by direct calculation and obtained (S(6,3)) from (S(5,3)) and a recursive bound; see preprint p. 1, lines 37–46. The paper's Theorem 1.1 is an all-(n) **upper bound** for (d=3), not the exact general (n=d+2) statement. In particular its (n=5) bound is weaker than (4π).

2. L. Fejes Tóth, *Über eine Punktverteilung auf der Kugel*, Acta Math. Acad. Sci. Hungar. 10 (1959), 13–19, [DOI 10.1007/BF02063286](https://doi.org/10.1007/BF02063286). This is the original work identified as [3] by Fodor–Vígh–Zarnócz. Its exact (S(5,3)) proof is reported to occur on p. 19 of the original paper. I verified the bibliographic record at the publisher and the summary in Fodor–Vígh–Zarnócz, **not** the original full text or its calculation; the accessible record alone cannot serve as a reconstructed proof.

3. D. Bilyk and R. W. Matzke, *On the Fejes Tóth problem about the sum of angles between lines*, [arXiv:1801.07837](https://arxiv.org/pdf/1801.07837), introduction pp. 1–2 and Theorem 1.3. They say Fejes Tóth confirmed the (S^2) case for (N≤6), then develop a general-dimensional upper bound for the **continuous normalized energy**. Theorem 1.3 is not an exact (N=d+2) discrete theorem. Their statement that the one-dimensional-sphere case is the only fully settled *all-(N)* case does not exclude the known isolated (N≤6) results in (S^2).

4. T. Lim and R. J. McCann, *On Fejes Tóth's conjectured maximizer for the sum of angles between lines*, [author-hosted paper](https://www.math.toronto.edu/mccann/papers/LimMcCann20a.pdf), introduction pp. 1–3. It formulates the all-(N) repeated-basis conjecture in (ℝ^{d+1}), states that for (d≥2) the general conjecture remains open, and proves a result for a different limiting objective (α=∞). It does not state an exact (N=d+2) theorem.

5. T. Zarnócz, [dissertation](https://doktori.bibl.u-szeged.hu/id/eprint/10222/1/__ZT_dissertation.pdf), Chapter 6, pp. 50–51, restates the 2016 paper and the known (n≤6,d=3) Fejes Tóth result. Theorem 2.2 there gives the exact planar formula, including (S(4,2)=2π), which supports the small base (N=4,d=2). Theorem 2.1 is a weaker general-(n) three-dimensional upper bound and does not prove the target.

## Search result and attribution limit

Targeted searches for `N=d+2`, `d+2`, and equivalent line-angle formulations in the primary papers above produced no exact general-(d) theorem or projection/sparse-graph proof. This is an **absence in the sources inspected**, not a proof that no such publication exists. The general projection argument in [proof.md](proof.md) was reconstructed in this workspace from the C4 argument and should be presented as such, without attributing it to Fejes Tóth or claiming novelty. The 1959 source supports only the historically reported (d=3,N≤5) calculation unless its full text is examined.

## Independent final audit of [proof.md](proof.md)

The §2 accounting is correct: removing (v_3) deletes only its two nonzero incident terms; normalization changes exactly (v_1v_2) and (v_4v_5), and creates (v_2v_4). Every other surviving inner product involving the two projected vectors was zero and stays zero. For (k≥6), (v_1,v_3,v_5) are pairwise orthogonal, and (v_2perp v_4). Positive path-edge coefficients ensure (0<B,C,U,V<π/2), nonzero residuals, and valid normalization.

In §3, total Gram nullity is **at least** two, which suffices: with at least two singular components, each has the auxiliary (π/2) deficiency; with exactly one, its nullity must be at least two, and the path/cycle recurrence forces it to be a cycle of nullity exactly two. A singular component has at least two vertices, so the C3 auxiliary bound applies. For (N=4,5), the possible sole singular cycles have lengths 3,4,5; the small-cycle analyses cover them. For a cycle of length (k≥6), its projected (k-1) vectors fit the strong-induction hypothesis because (k-1<N), even when (k<N). No mathematical gap found. This audit does not upgrade the result to a full Lean proof.
