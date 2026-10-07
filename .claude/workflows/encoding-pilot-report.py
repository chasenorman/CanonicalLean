#!/usr/bin/env python3
"""Usage: encoding-pilot-report.py <workflow output file> <name>

Writes each graded candidate of an encoding-pilot run as a patch (with its explanation as a header, which
`git apply` ignores), and a SUMMARY.md, to .claude/workflows/candidates/<name>/."""
import json
import os
import sys

output = json.load(open(sys.argv[1]))
result = output.get('result', output)
if isinstance(result, str):
    result = json.loads(result)
directory = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'candidates', sys.argv[2])
os.makedirs(directory, exist_ok=True)

candidates = result['candidates']
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

summary = [f'# {sys.argv[2]}', '']
for k, (c, patch) in enumerate(zip(candidates, patches)):
    if original(k) != k:
        continue
    evaluation = c.get('evaluation') or {}
    summary += [
        f"## {c['probability']:.2f} — {patch}",
        '',
        f"`{c['line']}`",
        '',
        f"- **Issue:** {c.get('issue')}",
        f"- **Implementation:** {c.get('implementation')}",
        f"- **Overseer:** {c.get('reason')}",
        f"- **Evaluation:** {(evaluation.get('output') or 'not evaluated').strip().splitlines()[0]}",
    ]
    if c.get('sameAs'):
        summary.append(f"- **Same as:** {c['sameAs']}")
    for j in duplicates.get(k, []):
        summary.append(f"- **Also found by** {patches[j]} (`{candidates[j]['line']}`): {candidates[j].get('implementation')}")
    summary.append('')

if result.get('declined'):
    summary += ['## Declined', '']
    for d in result['declined']:
        summary.append(f"- `{d['line']}`")
        summary += [f"  - {i['description']}" for i in d['issues'] if i['generalizable']]
    summary.append('')
if result.get('notes'):
    summary += ['## Notes', '']
    summary += [f"- `{n['line']}`: {n.get('note') or n.get('escalation')}" for n in result['notes']]
    summary.append('')
if result.get('notDispatched'):
    summary += ['## Not dispatched', ''] + [f"- `{line}`" for line in result['notDispatched']] + ['']

with open(os.path.join(directory, 'SUMMARY.md'), 'w') as f:
    f.write('\n'.join(summary))
print(directory)
