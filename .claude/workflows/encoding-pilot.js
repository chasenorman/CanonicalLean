export const meta = {
  name: 'encoding-pilot',
  description: 'Workers look for generalizable encoding oversights behind Canonical failures; an overseer grades their diffs for human review',
  whenToUse: 'After running encoding-pilot-setup.sh, with `lake exe debug ...` lines from `lake exe robustness`.',
  phases: [
    { title: 'Work', detail: 'one worker per failure: issues → generalizable oversights → at most one fix' },
    { title: 'Evaluate', detail: 'apply each diff to the Mathlib harness and build Results/ITP.lean (one at a time)' },
    { title: 'Oversee', detail: 'grade each diff, and handle escalations' },
  ],
}

// args: {
//   base: string          // commit printed by encoding-pilot-setup.sh
//   failures: string[]    // `lake exe debug ...` lines (already shuffled)
//   graded?: { description: string, probability: number, notes?: string }[]  // from earlier runs, with review notes
//   topK?: number         // how many graded candidates the overseer sees (default 20)
//   concurrency?: number  // workers running at once (default 6)
// }
const BASE = args.base
const FAILURES = args.failures
const TOP_K = args.topK ?? 20
const CONCURRENCY = args.concurrency ?? 6
const graded = [...(args.graded ?? [])]

const MAIN = '/Users/chasenorman/CanonicalLean'
const HARNESS = '/Users/chasenorman/Canonical/lean'
const PKG = `${HARNESS}/.lake/packages/Canonical`

const CANONICAL = `
Canonical is a type inhabitation solver for dependent type theory modulo reduction rules. CanonicalLean is a
Lean interface for Canonical that can be used to automatically prove theorems. The ToCanonical subsystem
translates Lean expressions into Canonical's intermediate expression representation. This encoding process is
responsible for providing the right representation to Canonical for search.

The main recursive translation is performed in Translate.lean. Canonical cannot synthesize typeclass instances,
so the Monomorphize subsystem is responsible for assigning instance arguments based on context. Canonical uses
backward search, so forward rules like structure projection can be difficult. The Destruct subsystem is
responsible for unpacking structures into their fields. Destruct is the pre-processing layer for CanonicalLean,
and can be used to handle cases where the goal type as written in Lean is not ideal for Canonical. Definitional
reduction rules for Canonical are obtained using Lean's equation compiler. Additionally, \`simp\` lemmas and
some premises are automatically converted to reduction rules for Canonical, to reduce the search space.
Obtaining the most shallow encoding of the goal type, with the least amount of unnecessary search directions,
is essential for the performance of Canonical.
`

const CRITERIA = `
Fixes are graded on:
- uniformity and generality: no high-specificity \`if\` conditions;
- simplicity: the amount of code reduction, or conceptual elegance;
- alignment with the code style: shallow use of library functions, fixes placed at the root cause.
`

const WORK = {
  type: 'object',
  properties: {
    outcome: { type: 'string', enum: ['fix', 'declined', 'escalation'] },
    issues: {
      type: 'array',
      description: 'every encoding issue you identified, whether or not you implemented a fix for it',
      items: {
        type: 'object',
        properties: {
          description: { type: 'string' },
          generalizable: { type: 'boolean', description: 'linked to a generalizable oversight' },
          reason: { type: 'string' },
        },
        required: ['description', 'generalizable', 'reason'],
      },
    },
    diff: { type: 'string', description: 'outcome fix: `git diff` of your one change' },
    description: { type: 'string', description: 'outcome fix: one sentence describing the change' },
    escalation: { type: 'string', description: 'outcome escalation: what is wrong, and what you observed' },
  },
  required: ['outcome', 'issues'],
}

const EVALUATION = {
  type: 'object',
  properties: {
    baseOk: { type: 'boolean', description: `${PKG} was at ${BASE} before applying` },
    applied: { type: 'boolean' },
    builds: { type: 'boolean', description: 'both lake commands succeeded' },
    output: { type: 'string', description: 'the last 40 lines of output of the first failing command, if any' },
  },
  required: ['baseOk', 'applied', 'builds'],
}

const GRADE = {
  type: 'object',
  properties: {
    probability: { type: 'number', minimum: 0, maximum: 1, description: 'that the author adopts this as a correct encoding improvement' },
    description: { type: 'string', description: 'one sentence describing the change' },
    sameAs: { type: 'string', description: 'the description of a listed candidate that makes the same change, if any' },
    reasons: { type: 'string' },
  },
  required: ['probability', 'description', 'reasons'],
}

const DECISION = {
  type: 'object',
  properties: {
    action: { type: 'string', enum: ['ignore', 'note', 'pause'] },
    note: { type: 'string', description: 'for the author, if action is note or pause' },
  },
  required: ['action'],
}

let paused = false
const notes = []
const notDispatched = []

// Evaluations share the harness's package directory, so they run one at a time.
let evaluations = Promise.resolve()
const evaluate = (diff, label) => {
  const run = evaluations.then(() => agent(`
Run exactly these commands, in order, each as a separate command, and report the results. Do not change
anything else, and do not try to fix failures.

1. git -C ${PKG} checkout -- .
2. git -C ${PKG} clean -fd
3. git -C ${PKG} rev-parse HEAD  (baseOk: whether this prints ${BASE})
4. git -C ${PKG} apply <<'CANONICAL_DIFF_END'
${diff}
CANONICAL_DIFF_END
5. lake -d ${HARNESS} build Canonical
6. lake -d ${HARNESS} env lean ${HARNESS}/Results/ITP.lean
7. git -C ${PKG} checkout -- .
8. git -C ${PKG} clean -fd

If step 3 or 4 fails, skip to step 7. Always run steps 7 and 8.`,
    { label: `evaluate ${label}`, phase: 'Evaluate', schema: EVALUATION, effort: 'low' }))
  evaluations = run.catch(() => {})
  return run
}

const topGraded = () => [...graded].sort((a, b) => b.probability - a.probability).slice(0, TOP_K)
  .map(g => `- (${g.probability.toFixed(2)}) ${g.description}${g.notes ? `\n  Author's notes: ${g.notes}` : ''}`).join('\n')

async function processFailure(line, i) {
  const work = await agent(`
${CANONICAL}
You are in a fresh git worktree of CanonicalLean. First copy the build directory from the main checkout,
\`cp -R ${MAIN}/.lake .lake\`, then run \`lake build debug\`.

This goal failed in a robustness sweep over the standard library:

  ${line}

Running it prints the goal, the Canonical problem (the +debug encoding), a witness (the known Lean proof
translated into the problem, not yet type-checked), the head symbols the witness uses that the problem does not
declare, and whether Canonical found a proof.

1. Identify the encoding issues that lead to this failure.
2. Keep only the issues linked to a generalizable oversight.
3. Attempt to implement a fix for at most one of them.
${CRITERIA}
Decline to implement a fix that does not meet these criteria; this will happen with substantial probability, and
declining is a good outcome. Feel free to deviate significantly from your initial conception of the issue as
better perspectives arise. A fix need not solve this goal, but it must be a justifiable improvement.

If the harness you are working in is not working as intended, or an unforeseen issue arises, stop and return an
escalation instead.`, { label: `work ${i}`, phase: 'Work', schema: WORK, isolation: 'worktree' })
  if (!work) return null
  if (work.outcome === 'escalation') {
    const decision = await agent(`
${CANONICAL}
You oversee a run in which workers look for generalizable encoding oversights behind failures of Canonical, and
propose fixes for human review. A worker on \`${line}\` escalated:

${work.escalation}

Decide whether to ignore this, note it for the author, or pause the run (no new workers are started; those
running finish).`, { label: `escalation ${i}`, phase: 'Oversee', schema: DECISION })
    if (decision?.action === 'note' || decision?.action === 'pause') notes.push({ line, escalation: work.escalation, note: decision.note })
    if (decision?.action === 'pause') paused = true
    return { line, work, decision }
  }
  if (work.outcome !== 'fix' || !work.diff?.trim()) return { line, work }

  const evaluation = await evaluate(work.diff, i)
  if (evaluation && !evaluation.baseOk) {
    paused = true
    notes.push({ line, note: `The harness package was not at ${BASE}; the run was paused.` })
  }
  const grade = await agent(`
${CANONICAL}
${CRITERIA}
A worker proposed this change after studying the failure \`${line}\`. Its description: "${work.description}".

${work.diff}

Applying it to the Mathlib harness and building Results/ITP.lean: ${evaluation ? (evaluation.builds ? 'succeeded' : `failed${evaluation.applied ? '' : ' (the diff did not apply)'}:\n${evaluation.output ?? ''}`) : 'not evaluated'}.

The highest-rated candidates graded so far:
${topGraded() || '(none yet)'}

Judge, from what is shown here, how likely the author is to adopt this as a correct encoding improvement, given
the stringent requirements on code simplicity. If a listed candidate makes the same change, give its description.`,
    { label: `grade ${i}`, phase: 'Oversee', schema: GRADE })
  if (grade) graded.push({ description: grade.description, probability: grade.probability })
  return { line, work, evaluation, grade }
}

// Workers are dispatched from a fixed number of lanes, so that a pause stops new workers from starting.
const results = []
let next = 0
await parallel(Array.from({ length: CONCURRENCY }, () => async () => {
  while (next < FAILURES.length && !paused) {
    const i = next++
    results[i] = await processFailure(FAILURES[i], i)
  }
}))
notDispatched.push(...FAILURES.slice(next))

const done = results.filter(Boolean)
const candidates = done.filter(r => r.grade).sort((a, b) => b.grade.probability - a.grade.probability)
log(`${candidates.length} graded candidates, ${done.filter(r => r.work.outcome === 'declined').length} declined, ${notes.length} notes`)
if (notDispatched.length) log(`Paused: ${notDispatched.length} failures were not dispatched`)
return {
  candidates: candidates.map(r => ({
    line: r.line, probability: r.grade.probability, description: r.grade.description, sameAs: r.grade.sameAs,
    reasons: r.grade.reasons, diff: r.work.diff, evaluation: r.evaluation, issues: r.work.issues,
  })),
  declined: done.filter(r => r.work.outcome === 'declined').map(r => ({ line: r.line, issues: r.work.issues })),
  notes,
  notDispatched,
}
