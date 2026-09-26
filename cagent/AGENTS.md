# Proof publishing

## Model routing

- Conserve usage: delegate simpler-looking proof tasks, routine lemmas, verification fixes, and packaging to `gpt-6-sol` subagents with `high` reasoning.
- Reserve Astra for difficult proof strategy, hard unresolved steps, or work where Sol has demonstrated a blocker. Do not default every task to Astra.
- When spawning with a model override, pass `model: "gpt-6-sol"`, `reasoning_effort: "high"`, and `fork_turns: "none"` or a positive turn count, together with a focused task and sufficient context.
- Preserve useful running work; apply this routing to new subtasks and safe handoffs without duplicating effort.

## Publishing workflow

- Whenever a cell is complete locally and audited against its exact task criteria, update its status and publish its reproducible package to remote main immediately; do not wait for harder cells. Publish already-completed verified proofs and useful verified increments too. Respect explicit approval-review blocks; do not route blocked publication through another worker.
- Organize packages under `cagent/<problem>/`, with clearly named cell folders or Lean modules. Keep each problem's README explicit about which cells and theorems are complete and which remain partial.
- Include Lean sources, required dependencies and pinned build configuration, exact verification commands, and relevant verification evidence. Do not rely on uncommitted files outside the published package.
- State the exact theorem proved and any assumptions or limitations. Do not present finite checks as a general theorem or an incomplete cell as complete. Do not use `sorry` or unproved custom axioms to claim completion.
- Maintain the repository root `README.md` as the authoritative global progress overview; `cagent/README.md` is only the package directory. Report the verified GitHub URL and commit after publication.
- Maintain the root README’s complete 24-cell table with exactly `Solved`, `Not solved`, or `Skipped`. `Solved` requires meeting the full cell requirements on the hackathon website. Complete written proofs and practical computational certificates qualify where the task permits them; values and constructions qualify where those are the requested hand-in. Lean completeness is a separate assurance field, not a universal status prerequisite. Partial proofs, finite cases of general claims, and upper bounds without required optimality remain `Not solved`. `Skipped` records an intentional scope decision, with its reason documented.
- Update the root README’s status, exact verified scope, remaining gap, proof links, and replay evidence together with the problem README whenever published coverage changes. Link exact theorem sources and verification evidence from the problem README. Audit assumptions against the original cell before changing status; never infer completion from filenames or successful compilation alone.
- Coordinate shared index/configuration edits and serialize git writes. Stage only owned files and agreed shared documentation; preserve unrelated work.
- GitHub publication is authorized. Submission to the hackathon platform is not authorized. Open-conjecture work remains paused.

## Publication format

Write judge-readable Markdown with `$...$` inline math and `$$...$$` display math, exact cell labels, full arguments, citations, and links to reproducible code and Lean evidence. The platform accepts Markdown with LaTeX math and an optional write-up link; a standalone `.tex` or PDF is not mandatory. Check rendered math and preserve the distinction between written, computational, and Lean proofs. Formatting preparation does not authorize platform submission.
