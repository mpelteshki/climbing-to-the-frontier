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

## Judge-ready writeup is part of task completion

Every problem task must prepare, verify, and publish its judge-ready writeup as part of the task itself. Do not treat the writeup as an optional follow-up or wait for a separate formatting request.

After the mathematical work, required witnesses, code, and verification are complete, consolidate them into one final judge-ready Markdown submission item for that task. This is the final deliverable, not merely a progress summary. Earlier drafts remain drafts until reconciled with the final verified results and published evidence.

- Use Markdown with `$...$` inline mathematics and `$$...$$` display mathematics, matching the hackathon submission editor. A separate LaTeX source or PDF is optional unless a cell explicitly requires it.
- State the exact problem and cell labels, answers, and truthful task status. Include the complete argument and every artifact required by that cell, such as explicit attaining binary vertex lists, constructions, or counterexamples. Do not replace required content with a progress report or a link to an unfinished proof.
- Cite reused published results, explain how their hypotheses match the task, and distinguish reused results from independently reconstructed arguments or computations.
- For computer-assisted proofs, explain why the computation proves the claim, provide the code, exact replay commands, and recorded runtime, and satisfy the task's runtime limit. Distinguish computational evidence, written proofs, and Lean certification, including any remaining premises or limitations.
- Check the rendered mathematical notation or its supported Markdown syntax, required lists and values, citations, and evidence links. Use self-contained links when the text is intended to be copied into the submission editor.
- Include the writeup in the package manifest and link it prominently from the problem README. The sole publisher integrates it with the relevant cell's status and evidence update and verifies publication on remote main.
- Apply this requirement to every P1–P4 task, including already completed cells whose writeup is missing. Preserve the distinction between a mathematically solved cell and an incomplete publication package; complete missing packaging before calling the task finished.
- Preparing or publishing a writeup does not authorize submitting it to the hackathon platform. Platform submission remains unauthorized.
