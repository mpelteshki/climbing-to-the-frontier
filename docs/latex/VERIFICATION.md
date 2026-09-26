# Verification and submission scope

Verified on 2026-09-26. Mathematical review and platform submission are separate: an “Under review” receipt confirms receipt, not organizer acceptance.

## Mathematical review

Independent Astra review approved the complete written solutions for P3 C1–C4, P4 C1–C5, and P1 C4–C5. P4 C5 claims the contiguous range through 14; its 24/30 exclusions remain conditional. Computation through 16 is not presented as a general Lean theorem.

P3 C5 now has a complete uniform upper/lower proof, independently audited by a fresh Astra reviewer. Its updated 13-page cell PDF includes the prerequisite lemmas and supersedes the earlier partial cell edition and the C5 section of the historical combined P3 PDF. [Audit evidence](../../cagent/p3/c5/audit.md). P3 C6 and P4 C6 are status-only. The C6 documents retain their incomplete labels and are not submitted as complete solutions. P1 C3 belongs to a separate owner and is excluded from this publishing batch. P1 C1–C2 and P2 C1–C4 were already solved on the platform.

## Document validation

The problem editions, cell editions, and complete P1 formalization appendix were exported with portable Tectonic. PDF text and page bounds were checked, with rendered pages inspected for mathematical notation and code glyphs. Bundled JuliaMono covers every non-ASCII code character in these sources. The source and output manifests record SHA-256 hashes.

The P1 appendix includes all 18 published Lean modules and describes their actual formalization scope. Complete written proofs do not imply that every general statement has been formalized in Lean.

## Computational replay

The self-contained P4 C4 archive was extracted into a fresh directory and replayed through 16. Both enumerators matched every recorded baseline exactly; the run completed successfully in 591.587 seconds. This is one observed runtime, not a portable performance guarantee. The smaller C5 package was independently extracted and replayed through 14 before submission. Its final run completed in 14.95 seconds.

The compact C4 submission uses the explicitly defined least-size/minimum-sum modulus method. Its three embedded source files are byte-identical to the reviewed implementations. The exact 108 displayed survivor lists were checked against both exhaustive algorithms through 16; the compact driver reported 296.609 seconds for searches and result checks (archive extraction/hash verification precedes that timer). It reports unresolved lists and conditional premises honestly rather than claiming every surviving modulus list has been decided.

Platform arguments use full inline Markdown/LaTeX text. Submission text is reviewed separately from the typeset editions; no public repository hosting is required.
