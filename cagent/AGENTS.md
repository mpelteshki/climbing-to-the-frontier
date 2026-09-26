# Proof publishing

## Model routing

- Conserve usage: delegate simpler-looking proof tasks, routine lemmas, verification fixes, and packaging to `gpt-6-sol` subagents with `high` reasoning.
- Reserve Astra for difficult proof strategy, hard unresolved steps, or work where Sol has demonstrated a blocker. Do not default every task to Astra.
- When spawning with a model override, pass `model: "gpt-6-sol"`, `reasoning_effort: "high"`, and `fork_turns: "none"` or a positive turn count, together with a focused task and sufficient context.
- Preserve useful running work; apply this routing to new subtasks and safe handoffs without duplicating effort.

## Publishing workflow

- Whenever a proof is complete and verified, commit and push its reproducible proof package to this repository on GitHub. Publish already-completed verified proofs too.
- Organize packages under `cagent/<problem>/`, with clearly named cell folders or Lean modules. Keep each problem's README explicit about which cells and theorems are complete and which remain partial.
- Include Lean sources, required dependencies and pinned build configuration, exact verification commands, and relevant verification evidence. Do not rely on uncommitted files outside the published package.
- State the exact theorem proved and any assumptions or limitations. Do not present finite checks as a general theorem or an incomplete cell as complete. Do not use `sorry` or unproved custom axioms to claim completion.
- Maintain `cagent/README.md` as the package index. Report the verified GitHub URL and commit after publication.
- Maintain its problem-by-cell grid with exactly `Solved`, `Not solved`, or `Skipped`. `Solved` requires a verified Lean proof of the full cell statement; partial proofs, finite cases of general claims, and upper bounds without required optimality remain `Not solved`. `Skipped` records an intentional scope decision, with its reason documented.
- Update the shared grid, verified-progress summary, and problem README together whenever published coverage changes. Link exact theorem sources and verification evidence from the problem README. Audit assumptions against the original cell before changing status; never infer completion from filenames or successful compilation alone.
- Coordinate shared index/configuration edits and serialize git writes. Stage only owned files and agreed shared documentation; preserve unrelated work.
- GitHub publication is authorized. Submission to the hackathon platform is not authorized. Open-conjecture work remains paused.
