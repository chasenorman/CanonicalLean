#!/usr/bin/env python3
"""Usage: encoding-pilot-report.py <run id>

Reads the journal of an encoding-pilot run, which the workflow runner writes as each agent finishes, so this can
be run during the run as well as after it. Writes each graded candidate as a patch (with its explanation as a
header, which `git apply` ignores), and a SUMMARY.md, to .claude/workflows/candidates/<run id>/."""
import glob
import json
import os
import re
import sys

run = sys.argv[1]
journals = glob.glob(os.path.expanduser(f'~/.claude/projects/*/*/subagents/workflows/{run}/journal.jsonl'))
if not journals:
    sys.exit(f'No journal found for {run}.')
transcripts = os.path.dirname(journals[0])
directory = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'candidates', run)
os.makedirs(directory, exist_ok=True)
for old in glob.glob(os.path.join(directory, '*.patch')):
    os.remove(old)

# Each agent's label starts with the index of its failure (in older runs, after `work`, `grade` or `escalation`).
# Its phase tells a worker from an overseer, and an overseer's result tells a grade from an escalation decision.
def index(label):
    return next(int(token) for token in label.split() if token.isdigit())


phases, results = {}, {}
for entry in map(json.loads, open(journals[0])):
    if entry['type'] == 'started':
        phases[entry['agentId']] = (entry['phase'], index(entry['label']))
    elif entry['type'] == 'result' and entry['agentId'] in phases:
        phase, i = phases[entry['agentId']]
        kind = 'work' if phase == 'Work' else 'grade' if 'probability' in (entry['result'] or {}) else 'escalation'
        results.setdefault(i, {})[kind] = entry['result']
started = {i for phase, i in phases.values()}
work_ids = {i: agent for agent, (phase, i) in phases.items() if phase == 'Work'}


def strings(value):
    """Every string inside a decoded JSON value."""
    if isinstance(value, str):
        yield value
    elif isinstance(value, (list, dict)):
        for child in (value.values() if isinstance(value, dict) else value):
            yield from strings(child)


def failure(i):
    """The `lake exe debug` line given to worker `i`, from its prompt."""
    with open(os.path.join(transcripts, f'agent-{work_ids[i]}.jsonl')) as f:
        for text in strings([json.loads(line) for line in f]):
            if match := re.search(r'standard library:\s*(lake exe debug .*)', text):
                return match.group(1)
    return '?'


candidates = sorted(
    [{'line': failure(i), **r['work'], **r['grade']} for i, r in results.items() if r.get('grade')],
    key=lambda c: -c['probability'])
patches = [f"{k:02d}-{c['probability']:.2f}.patch" for k, c in enumerate(candidates, 1)]
for c, patch in zip(candidates, patches):
    header = '\n'.join(f'# {line}' for line in (c.get('explanation') or '').splitlines())
    with open(os.path.join(directory, patch), 'w') as f:
        f.write(header + '\n\n' + c['diff'].rstrip('\n') + '\n')


def original(k):
    """The index of the candidate that candidate `k` duplicates (following chains), or `k` if none in this run."""
    seen = {k}
    while same := candidates[k].get('sameAs'):
        matches = [j for j, c in enumerate(candidates) if c.get('issue') and same.startswith(c['issue']) and j not in seen]
        if not matches:
            break
        k = matches[0]
        seen.add(k)
    return k


duplicates = {}
for k in range(len(candidates)):
    if (o := original(k)) != k:
        duplicates.setdefault(o, []).append(k)

finished = [i for i, r in results.items() if 'work' in r]
summary = [f'# {run}', '', f'{len(finished)} of {len(started)} started workers finished; {len(candidates)} candidates graded.', '']
for k, (c, patch) in enumerate(zip(candidates, patches)):
    if original(k) != k:
        continue
    summary += [
        f"## {c['probability']:.2f} — {patch}",
        '',
        f"`{c['line']}`",
        '',
        f"- **Issue:** {c.get('issue')}",
        f"- **Implementation:** {c.get('implementation')}",
        f"- **Overseer:** {c.get('reason')}",
        f"- **Evaluation:** {(c.get('evaluation') or 'not evaluated').strip().splitlines()[0]}",
    ]
    if c.get('sameAs'):
        summary.append(f"- **Same as:** {c['sameAs']}")
    for j in duplicates.get(k, []):
        summary.append(f"- **Also found by** {patches[j]} (`{candidates[j]['line']}`): {candidates[j].get('implementation')}")
    summary.append('')

declined = [i for i in sorted(finished) if results[i]['work'].get('outcome') == 'declined']
if declined:
    summary += ['## Declined', '']
    for i in declined:
        summary.append(f"- `{failure(i)}`")
        summary += [f"  - {issue['description']}" for issue in results[i]['work']['issues'] if issue['generalizable']]
    summary.append('')
escalated = [i for i in sorted(finished) if results[i]['work'].get('outcome') == 'escalation']
paused = [i for i, r in results.items() if (r.get('grade') or {}).get('exitCode') == 1]
if escalated or paused:
    summary += ['## Notes', '']
    for i in escalated:
        decision = results[i].get('escalation') or {}
        summary.append(f"- `{failure(i)}` ({decision.get('action', 'undecided')}): {decision.get('note') or results[i]['work'].get('escalation')}")
    summary += [f"- `{failure(i)}`: the harness package was not clean; the run was paused." for i in paused]
    summary.append('')

set_aside = [i for i in sorted(finished) if results[i]['work'].get('outcome') == 'deferred']
if set_aside:
    summary += ['## Set aside as deferred', '']
    summary += [f"- `{failure(i)}`: {results[i]['work'].get('deferredBy')}" for i in set_aside]
    summary.append('')

# Deferrals, recorded for later runs (their `deferred` argument) in encoding-pilot-deferred.jsonl.
deferring = [i for i in sorted(finished) if (results[i]['work'].get('defer') or {}).get('constants')]
if deferring:
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'encoding-pilot-deferred.jsonl')
    known = [json.loads(line)['constants'] for line in open(path)] if os.path.exists(path) else []
    summary += ['## Deferrals', '']
    for i in deferring:
        defer = results[i]['work']['defer']
        summary.append(f"- `{failure(i)}`: goals mentioning {defer['constants']}. {defer['reason']}")
        if sorted(defer['constants']) not in [sorted(k) for k in known]:
            known.append(defer['constants'])
            with open(path, 'a') as f:
                f.write(json.dumps({'constants': defer['constants'], 'reason': defer['reason'], 'run': run},
                                   ensure_ascii=False) + '\n')
    summary.append('')

with open(os.path.join(directory, 'SUMMARY.md'), 'w') as f:
    f.write('\n'.join(summary))
print(directory)
