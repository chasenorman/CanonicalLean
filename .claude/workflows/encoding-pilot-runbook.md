# Encoding pilot run book

How to run the encoding pilot over the failures of a robustness sweep. Paths are relative to the CanonicalLean root,
`/Users/chasenorman/CanonicalLean`; run commands from there.

## What it does

`encoding-pilot.js` gives each failure of `lake exe robustness` to a worker agent, in a git worktree of its own. The
worker identifies the encoding issues behind the failure, keeps those linked to a generalizable oversight, and
attempts a fix for at most one of them, or declines. An overseer builds each fix in the Mathlib harness
(`~/Canonical/lean`) and grades it. A worker can also defer an oversight that will affect other goals; later workers
whose goals fail because of it set them aside at once.

## Running it

1. Set up, which checks that the harness builds the committed Canonical, and prints the base commit:
   ```bash
   bash .claude/workflows/encoding-pilot-setup.sh
   ```
2. Launch the workflow with the Workflow tool, with `args` a JSON object of:
   - `base`: the commit printed by the setup;
   - `failures`: the `lake exe debug …` lines of the sweep, as strings, in order (for the seed-2 sweep, the first
     600 lines of `robustness-seed2.txt`; the workflow stops starting failures as it nears its limit of 1000 agents);
   - `graded`: the contents of `.claude/workflows/encoding-pilot-graded.json`;
   - `deferred`: the lines of `.claude/workflows/encoding-pilot-deferred.jsonl`, as objects, if it exists.
   ```
   Workflow({ scriptPath: "/Users/chasenorman/CanonicalLean/.claude/workflows/encoding-pilot.js", args: { … } })
   ```
   Note the run id it returns (`wf_…`). It takes about 8 hours.
3. During and after the run, write out the candidates:
   ```bash
   python3 .claude/workflows/encoding-pilot-report.py <run id> <run id>
   ```
   This writes `.claude/workflows/candidates/<run id>/`: a patch per candidate and `SUMMARY.md` (candidates by grade,
   declined failures, failures set aside, notes, and deferrals), and records the deferrals in
   `encoding-pilot-deferred.jsonl` for later runs.

## Rules

- Do not change any code or the workflow.
- The workflow pauses itself when an escalation's overseer decides to, or when the harness is not clean at the base.
  Then report the notes in the workflow's result.

## Final report

The run id; how many failures were worked, and of those how many were fixed, declined, set aside as deferred, or
escalated; the highest graded candidates (their issue, implementation and grade); and the deferrals made.
