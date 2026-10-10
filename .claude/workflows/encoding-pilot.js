export const meta = {
  name: 'encoding-pilot',
  description: 'Workers look for generalizable encoding oversights behind Canonical failures; an overseer grades their diffs for human review',
  whenToUse: 'After running encoding-pilot-setup.sh, with `lake exe debug ...` lines from `lake exe robustness`.',
  phases: [
    { title: 'Work', detail: 'one worker per failure: issues → generalizable oversights → at most one fix' },
    { title: 'Oversee', detail: 'build each diff in the Mathlib harness and grade it, and handle escalations' },
  ],
}

// args: {
//   base: string          // commit printed by encoding-pilot-setup.sh
//   failures: string[]    // `lake exe debug ...` lines (already shuffled)
//   deferred?: { constants: string[], reason: string }[]  // deferrals from earlier runs (encoding-pilot-deferred.jsonl)
//   graded?: { issue: string, implementation: string, probability: number, notes?: string }[]  // with review notes
//   topK?: number         // how many graded candidates the overseer sees (default 20)
//   concurrency?: number  // workers running at once (default 10)
//   agentLimit?: number   // agents the run may start (default 990, under the workflow limit of 1000)
// }
// The candidates so far can be written out, during or after the run, with `encoding-pilot-report.py <run id>`.
const BASE = args.base
const FAILURES = args.failures
/** Oversights that workers have deferred, from earlier runs and this one; each worker checks its goal against them. */
const deferrals = [...(args.deferred ?? [])]
const TOP_K = args.topK ?? 20
const CONCURRENCY = args.concurrency ?? 10
const AGENT_LIMIT = args.agentLimit ?? 990
// No new failure is started once this few agents remain, to leave room for those running to be graded.
const RESERVE = 2 * CONCURRENCY

/** Agents started so far. */
let agents = 0

/** `agent`, counted against `AGENT_LIMIT`; `null` if the limit is reached. */
async function counted(prompt, opts) {
  if (agents >= AGENT_LIMIT) return null
  agents++
  return agent(prompt, opts)
}
const graded = [...(args.graded ?? [])]

const MAIN = '/Users/chasenorman/CanonicalLean'
const EVALUATE = `${MAIN}/.claude/workflows/encoding-pilot-evaluate.sh`
const WORKER = `${MAIN}/.claude/workflows/encoding-pilot-worker.sh`
const GRADED = `${MAIN}/.claude/workflows/encoding-pilot-graded.json`

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
    outcome: { type: 'string', enum: ['fix', 'declined', 'deferred', 'escalation'] },
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
    issue: { type: 'string', description: 'outcome fix: one sentence stating the issue' },
    implementation: { type: 'string', description: 'outcome fix: one sentence stating how the change addresses it' },
    explanation: { type: 'string', description: 'outcome fix: the oversight the change addresses, and why it is a justifiable improvement' },
    escalation: { type: 'string', description: 'outcome escalation: what is wrong, and what you observed' },
    deferredBy: { type: 'string', description: 'outcome deferred: the reason of the deferral that covers this goal' },
    defer: {
      type: 'object',
      description: 'only if confident: an oversight that later workers should recognize and set aside',
      properties: {
        constants: { type: 'array', items: { type: 'string' }, description: 'constants that the goals it affects mention' },
        reason: { type: 'string', description: 'the oversight that makes such goals fail' },
      },
      required: ['constants', 'reason'],
    },
  },
  required: ['outcome', 'issues'],
}

const GRADE = {
  type: 'object',
  properties: {
    probability: { type: 'number', minimum: 0, maximum: 1, description: 'that the author adopts this as a correct encoding improvement' },
    reason: { type: 'string', description: 'one sentence' },
    sameAs: { type: 'string', description: 'the issue of a listed candidate that makes the same change, if any' },
    exitCode: { type: 'integer', description: 'of the build command' },
    evaluation: { type: 'string', description: 'the output of the build command' },
  },
  required: ['probability', 'reason', 'exitCode', 'evaluation'],
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

const topGraded = () => [...graded].sort((a, b) => b.probability - a.probability).slice(0, TOP_K)
  .map(g => `- (${g.probability.toFixed(2)}) ${g.issue} ${g.implementation}${g.notes ? `\n  Author's notes: ${g.notes}` : ''}`).join('\n')

// The theorem a `lake exe debug` line is about, without its shell quoting.
const theorem = line => line.split(' ')[3].replace(/^'|'$/g, '').replace(/'\\''/g, "'")

async function processFailure(line, i) {
  const name = theorem(line)
  const work = await counted(`
${CANONICAL}
You are in a fresh git worktree of CanonicalLean. First run \`bash ${WORKER} ${BASE}\`, which sets it up.

This goal failed in a robustness sweep over the standard library:

  ${line}

Running it prints the goal, the Canonical problem (the +debug encoding), a witness (the known Lean proof
translated into the problem, not yet type-checked), the head symbols the witness uses that the problem does not
declare, and whether Canonical found a proof. Keep any scratch files inside your worktree.

Fixes proposed in earlier runs, with the author's decisions, are in ${GRADED}. Do not propose one again unless
you address the author's notes on it.

These oversights have been deferred, until they are fixed:
${deferrals.map(d => `- ${d.reason} (goals mentioning ${d.constants.join(', ')})`).join('\n') || '(none)'}
If this goal fails because of one of them, return the outcome \`deferred\` straight away, giving its reason in
\`deferredBy\`.

1. Identify the encoding issues that lead to this failure.
2. Keep only the issues linked to a generalizable oversight.
3. Attempt to implement a fix for at most one of them.
${CRITERIA}
Decline to implement a fix that does not meet these criteria; this will happen with substantial probability, and
declining is a good outcome. Feel free to deviate significantly from your initial conception of the issue as
better perspectives arise. A fix need not solve this goal, but it must be a justifiable improvement.

If an oversight you identified will make Canonical fail on other goals, whether or not you fixed it, you may defer
it: give in \`defer\` the reason, and the constants that the goals it affects mention. Later workers will set those
goals aside. Only do so if you are confident.

If the harness you are working in is not working as intended, or an unforeseen issue arises, stop and return an
escalation instead.`, { label: `${i} ${name}`, phase: 'Work', schema: WORK, isolation: 'worktree' })
  if (!work) return null
  log(work.outcome === 'fix' ? `${name}: ${work.issue} ${work.implementation}` : `${name}: ${work.outcome}`)
  if (work.defer?.constants?.length) {
    deferrals.push(work.defer)
    log(`${name}: deferring goals that mention ${work.defer.constants.join(', ')}: ${work.defer.reason}`)
  }
  if (work.outcome === 'escalation') {
    const decision = await counted(`
${CANONICAL}
You oversee a run in which workers look for generalizable encoding oversights behind failures of Canonical, and
propose fixes for human review. A worker on \`${line}\` escalated:

${work.escalation}

Decide whether to ignore this, note it for the author, or pause the run (no new workers are started; those
running finish).`, { label: `${i} ${name}`, phase: 'Oversee', schema: DECISION })
    if (decision?.action === 'note' || decision?.action === 'pause') notes.push({ line, escalation: work.escalation, note: decision.note })
    if (decision?.action === 'pause') paused = true
    log(`${name}: escalation, ${decision?.action ?? 'undecided'}`)
    return { line, work, decision }
  }
  if (work.outcome !== 'fix' || !work.diff?.trim()) return { line, work }

  const grade = await counted(`
${CANONICAL}
${CRITERIA}
A worker proposed this change after studying the failure \`${line}\`.
Issue: ${work.issue}
Implementation: ${work.implementation}

Its explanation:
${work.explanation ?? '(none given)'}

First, build it in the Mathlib harness by running exactly this command, with a 10 minute timeout. Exit code 75
means the harness was busy; run it again. Report its exit code and output.

bash ${EVALUATE} ${BASE} <<'CANONICAL_DIFF_END'
${work.diff}
CANONICAL_DIFF_END

The highest-rated candidates graded so far:
${topGraded() || '(none yet)'}

Judge, from what is shown here, how likely the author is to adopt this as a correct encoding improvement, given
the stringent requirements on code simplicity. If a listed candidate makes the same change, give its issue.`,
    { label: `${i} ${name}`, phase: 'Oversee', schema: GRADE })
  if (grade) log(`${name}: ${grade.probability.toFixed(2)}${grade.sameAs ? ' (duplicate)' : ''}. ${grade.reason}`)
  if (grade?.exitCode === 1) {
    paused = true
    notes.push({ line, note: `The harness package was not clean at ${BASE}; the run was paused.\n${grade.evaluation}` })
  }
  // A duplicate is already represented in the list by the candidate it duplicates.
  if (grade && !grade.sameAs) graded.push({ issue: work.issue, implementation: work.implementation, probability: grade.probability })
  return { line, work, grade }
}

// Workers are dispatched from a fixed number of lanes, so that a pause stops new workers from starting.
const results = []
let next = 0
await parallel(Array.from({ length: CONCURRENCY }, () => async () => {
  while (next < FAILURES.length && !paused && agents < AGENT_LIMIT - RESERVE) {
    const i = next++
    results[i] = await processFailure(FAILURES[i], i)
  }
}))
notDispatched.push(...FAILURES.slice(next))

const done = results.filter(Boolean)
const candidates = done.filter(r => r.grade).sort((a, b) => b.grade.probability - a.grade.probability)
log(`${candidates.length} graded candidates, ${done.filter(r => r.work.outcome === 'declined').length} declined, ${notes.length} notes`)
if (notDispatched.length) log(`${paused ? 'Paused' : 'Agent limit reached'}: ${notDispatched.length} failures were not dispatched`)
// Everything else is in the journal; `encoding-pilot-report.py` writes it out.
return {
  candidates: candidates.length,
  declined: done.filter(r => r.work.outcome === 'declined').length,
  deferred: done.filter(r => r.work.outcome === 'deferred').length,
  escalations: done.filter(r => r.work.outcome === 'escalation').length,
  notes,
  deferrals: deferrals.slice((args.deferred ?? []).length),
  notDispatched: notDispatched.length,
  agents,
}
