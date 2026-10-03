import * as React from 'react'
import { useRpcSession, EditorContext, EnvPosContext } from '@leanprover/infoview'

// ===== SHARED between typewriter.js and canonical2.js — keep identical (copy-paste to sync) =====
function tokenize(s) {
  return s.match(/([^;,\(\)\{\}\[\]\s]+|[;,\(\)\{\}\[\]]|\s+)/g) || [];
}

const keyword = "var(--vscode-lean4-infoView\\.goalCount)"
const paren = "var(--vscode-editorBracketHighlight-foreground1)"
const colorMap = {
  have: keyword, exact: keyword, by: keyword, simp_all: keyword, only: keyword,
  simp: keyword, simpa: keyword, grind: keyword, fun: keyword, clear: keyword,
  "(": paren, ")": paren, "[": paren, "]": paren, "{": paren, "}": paren
}

function getCols(el) {
  if (!el) return 80;
  const ctx = document.createElement("canvas").getContext("2d");
  ctx.font = getComputedStyle(el).font;
  return Math.floor(el.getBoundingClientRect().width / ctx.measureText("0").width);
}
// ===== END SHARED ==============================================================

// The token stream is the `have` tool's argument JSON. Return the (partial)
// string value of `key`, JSON-unescaped, or null before that field begins.
function partialField(str, key) {
  const m = new RegExp(`"${key}"\\s*:\\s*"`).exec(str);
  if (m === null) return null;
  let out = "";
  for (let i = m.index + m[0].length; i < str.length; i++) {
    const c = str[i];
    if (c === '"') break;
    if (c !== "\\") { out += c; continue; }
    const e = str[i + 1];
    if (e === undefined) break;                    // dangling backslash: wait for more
    if (e === "u") {
      const hex = str.slice(i + 2, i + 6);
      if (hex.length < 4) break;                   // incomplete \uXXXX
      out += String.fromCharCode(parseInt(hex, 16)); i += 5; continue;
    }
    out += { n: "\n", t: "\t", r: "\r", b: "\b", f: "\f" }[e] ?? e;
    i++;
  }
  return out;
}

const controlStyle = {
    border: 'none',
    font: 'inherit',
    outline: 'inherit',
    padding: '5px 10px',
    borderRadius: '8.5px',
    minWidth: '30px',
    backgroundColor: 'rgb(240, 240, 240)',
    color: 'rgb(30, 30, 30)',
    cursor: 'pointer'
}

// Borderless native selects put the arrow flush against the edge, so draw our own.
const chevron = "url(\"data:image/svg+xml;utf8,<svg xmlns='http://www.w3.org/2000/svg' width='10' height='6' viewBox='0 0 10 6'><path d='M1 1l4 4 4-4' fill='none' stroke='rgb(30,30,30)' stroke-width='1.5' stroke-linecap='round'/></svg>\")"
const selectStyle = {
    ...controlStyle,
    appearance: 'none',
    WebkitAppearance: 'none',
    paddingRight: '28px',
    backgroundImage: chevron,
    backgroundRepeat: 'no-repeat',
    backgroundPosition: 'right 10px center'
}

// Models offered per provider kind; the first is the default when switching kinds.
const MODELS = {
    Claude: [['Haiku', 'claude-haiku-4-5-20251001'], ['Sonnet', 'claude-sonnet-5'], ['Opus', 'claude-opus-5'], ['Fable', 'claude-fable-5-1']],
    Codex: [['Luna', 'gpt-5.6-luna'], ['Terra', 'gpt-5.6-terra'], ['Sol', 'gpt-5.6-sol'], ['Astra', 'gpt-6-astra']],
}
// A choice with a valid model for its kind (saved choices may predate the lists).
function normalize(choice) {
    const models = MODELS[choice.kind]
    if (!models) return { ...choice, kind: 'Local' }
    return models.some(m => m[1] === choice.model) ? choice : { ...choice, model: models[0][1] }
}

export default function (props) {
    const style = document.createElement('style');
    style.textContent = `
    @keyframes animateIn {
    from { opacity: 0; }
    to   { opacity: 1; }
    }
    @keyframes pulse {
    0%   { opacity: 0.2; transform: scale(0.85); }
    50%  { opacity: 1;   transform: scale(1); }
    100% { opacity: 0.2; transform: scale(0.85); }
    }
    `;
    document.head.appendChild(style);

    const pos = React.useContext(EnvPosContext)
    const rs = useRpcSession()
    const editorConnection = React.useContext(EditorContext)

    const ref = React.createRef();
    const thinkingRef = React.useRef(null);
    const [out, setOut] = React.useState('')
    const [print, setPrint] = React.useState('')
    const [tokenText, setTokenText] = React.useState('')
    const [prefilling, setPrefilling] = React.useState(false)
    const [thinkingText, setThinkingText] = React.useState('')
    const [errorText, setErrorText] = React.useState('')
    const [name, setName] = React.useState(null)
    const [progressPct, setProgressPct] = React.useState('')
    const [statusMsg, setStatusMsg] = React.useState('')
    const [totalCost, setTotalCost] = React.useState(0)
    // `provider` is what the controls show; `active` is what was submitted to run
    // (Local runs on its own, Claude/Codex wait for Start).
    const [provider, setProvider] = React.useState(() => normalize(props.provider))
    const [active, setActive] = React.useState(() => {
        const p = normalize(props.provider); return p.kind === 'Local' ? p : null
    })

    React.useEffect(() => {
        if (active === null) return
        let stopped = false
        let cols = getCols(ref.current)
        let currentTask = null
        async function run() {
            var state = props.state
            while (!stopped) {
                setTokenText('')
                setErrorText('')
                setPrefilling(false)
                setOut(await rs.call('Canonical2.leanStringRpc', {
                    val: {
                        expr: props.expr,
                        width: cols,
                        indent: 0,
                        column: 0,
                        exact: false
                    },
                    ctx: props.ctx,
                    state: state
                }))

                const mvar = await rs.call('Canonical2.nextGoal', {
                    val: props.expr,
                    ctx: props.ctx,
                    state: state
                })

                if (mvar === undefined) {
                    let str = await rs.call('Canonical2.leanStringRpc', {
                        val: {
                            expr: props.expr,
                            width: props.width,
                            indent: props.indent,
                            column: props.column,
                            exact: true
                        },
                        ctx: props.ctx,
                        state: state
                    })
                    editorConnection.api.applyEdit({
                        changes: { [pos.uri]: [{ range: props.range, newText: str }] }
                    })
                    break;
                }
                setName(mvar.mvar)
                
                const taskHandle = await rs.call('Canonical2.step', {
                    val: { mvar: mvar.mvar, pipe: props.pipe, provider: active },
                    ctx: props.ctx,
                    state: state
                })
                if (stopped) {
                    rs.call('Canonical2.cancel', taskHandle).catch(() => {})
                    break
                }
                currentTask = taskHandle
                state = await rs.call('Canonical2.get', taskHandle)
                currentTask = null
            }
        }
        run()
        return function () {
            stopped = true
            if (currentTask) {
                rs.call('Canonical2.cancel', currentTask).catch(() => {})
                currentTask = null
            }
        }
    }, [active])

    function clearOutput() {
        setPrint(''); setThinkingText(''); setErrorText(''); setTokenText(''); setPrefilling(false)
    }

    function selectKind(kind) {
        const next = normalize({ ...provider, kind })
        setProvider(next)
        clearOutput()
        setActive(kind === 'Local' ? next : null)
    }

    function start() {
        clearOutput()
        setActive({ ...provider })
    }

    React.useEffect(() => {
        let stopped = false
        let generateSeen = true

        async function recvLoop() {
            while (!stopped) {
                const msg = await rs.call('Canonical2.recv', props.pipe)
                if ('prefill' in msg) {
                    setPrefilling(true)
                    setTokenText('')
                    setThinkingText('')
                    setErrorText('')
                } else if ('error' in msg) {
                    setErrorText(String(msg.error))
                } else if ('token' in msg) {
                    if (generateSeen) {
                        setTokenText(function (prev) { return prev + String(msg.token) })
                    }
                } else if ('thinking' in msg) {
                    setThinkingText(function (prev) { return prev + String(msg.thinking) })
                } else if ('generate' in msg) {
                    generateSeen = true
                } else if ('cost' in msg) {
                    setTotalCost(function (prev) { return prev + Number(msg.cost) })
                } else if ('print' in msg) {
                    setPrint(String(msg.print))
                } else if ('status' in msg) {
                    setStatusMsg(String(msg.status))
                } else if ('progress' in msg) {
                    setProgressPct(String(msg.progress))
                }
            }
        }

        recvLoop()
        return function () { stopped = true }
    }, [rs, props.pipe])

    const prevScrollHeight = React.useRef(0);
    React.useEffect(() => {
        const el = thinkingRef.current;
        if (!el) return;
        // Only auto-scroll if the user was already at (or near) the previous
        // bottom; otherwise leave them where they scrolled to.
        const wasAtBottom = el.scrollTop + el.clientHeight >= prevScrollHeight.current - 10;
        if (wasAtBottom) el.scrollTop = el.scrollHeight;
        prevScrollHeight.current = el.scrollHeight;
    }, [thinkingText])

    if (statusMsg !== '') {
        const pct = progressPct === '' ? 0 : Number(progressPct)
        return React.createElement('div', {
            style: {
                margin: '20px'
            }
        },
            React.createElement('div', null, statusMsg),
            React.createElement('div', {
                style: {
                    width: '100%',
                    height: '4px',
                    backgroundColor: 'rgba(128, 128, 128, 0.2)',
                    borderRadius: '2px',
                    overflow: 'hidden',
                    marginTop: '8px'
                }
            },
                React.createElement('div', {
                    style: {
                        width: `${pct}%`,
                        height: '100%',
                        backgroundColor: 'currentColor',
                        transition: 'width 200ms ease-out'
                    }
                })
            ),
            progressPct !== '' && React.createElement('div', {
                style: { marginTop: '4px', fontSize: '0.85em', opacity: 0.7 }
            }, `${pct}%`)
        )
    }

    const partialName = partialField(tokenText, "name"), partialType = partialField(tokenText, "type")
    const toLoading = partialName === null && partialType === null ? '__loading__'
        : `have ${partialName || '__loading__'} : ${partialType || '__loading__'}`
    const delimiter = name === null ? '\u0000' : "?" + name;

    const [before, after = ""] = out.split(delimiter, 2);

    const tokens = [
        ...tokenize(before).map(t => [t, false]),
        ...(name === null ? [] : tokenize(toLoading).map(t => [t, true])),
        ...tokenize(after).map(t => [t, false]),
    ];

    return React.createElement(
        'div',
        null,
        React.createElement( 'div', { ref: ref, style: {
                margin: '20px',
                fontFamily: 'Menlo, Monaco, "Courier New", monospace',
                whiteSpace: 'pre',
                overflow: 'hidden'
            } },
            tokens.map((tok, i) => {
                if (/^\s+$/.test(tok[0])) {
                    return React.createElement('span', { key: i }, tok[0]);
                } else if (tok[0] === "__loading__") {
                    return React.createElement('span', {
                        key: i,
                        style: {
                        display: 'inline-block',
                        width: '0.9em',
                        height: '0.9em',
                        borderRadius: '50%',
                        backgroundColor: 'currentColor',
                        ...(prefilling && { animation: 'pulse 1.2s ease-in-out infinite' }),
                        verticalAlign: 'text-bottom'
                        }
                    });
                } else {
                    return React.createElement('span', {
                            key: i,
                            style: {
                                display: 'inline-block',
                                opacity: tok[1] ? 0 : 1,
                                ...(tok[1] && {
                                    animation: `animateIn 500ms ease-out forwards`,
                                }),
                                ...(colorMap[tok[0]] && { color: colorMap[tok[0]] })
                            }
                        },
                        tok[0].startsWith("?") ? "?_" : tok[0]
                    )
                }
            })
        ),
        
        thinkingText !== '' && React.createElement('div', {
            ref: thinkingRef,
            style: {
                margin: '0 20px 8px 20px',
                fontFamily: 'Menlo, Monaco, "Courier New", monospace',
                fontSize: '0.85em',
                opacity: 0.6,
                whiteSpace: 'pre-wrap',
                height: '200px',
                overflow: 'auto'
            }
        }, thinkingText),
        errorText !== '' && React.createElement('div', {
            style: {
                margin: '0 20px 8px 20px',
                fontFamily: 'Menlo, Monaco, "Courier New", monospace',
                fontSize: '0.85em',
                color: 'var(--vscode-errorForeground, #f14c4c)',
                whiteSpace: 'pre-wrap',
                maxHeight: '200px',
                overflow: 'auto'
            }
        }, errorText),
        print !== '' && React.createElement('div', {
            style: {
                margin: '0 20px 8px 20px',
                fontSize: '0.85em',
                opacity: 0.7
            }
        }, print),
        React.createElement('div', { style: { margin: '0 20px 8px 20px', display: 'flex', gap: '10px', flexWrap: 'wrap', alignItems: 'center' } },
            React.createElement('select', { style: selectStyle, value: provider.kind, onChange: e => selectKind(e.target.value) },
                ['Local', 'Claude', 'Codex'].map(k => React.createElement('option', { key: k, value: k }, k))),
            MODELS[provider.kind] && React.createElement('select', {
                style: selectStyle,
                value: provider.model,
                onChange: e => setProvider({ ...provider, model: e.target.value })
            }, MODELS[provider.kind].map(([label, id]) => React.createElement('option', { key: id, value: id }, label))),
            MODELS[provider.kind] && React.createElement('button', { style: controlStyle, onClick: start },
                active === null ? 'Start' : 'Restart')
        ),
        MODELS[provider.kind] && React.createElement('textarea', {
            value: provider.prompt,
            placeholder: 'Prompt',
            rows: 2,
            onChange: e => setProvider({ ...provider, prompt: e.target.value }),
            style: { ...controlStyle, cursor: 'text', display: 'block', margin: '0 20px 8px 20px',
                width: 'calc(100% - 40px)', boxSizing: 'border-box', resize: 'vertical' }
        }),
        totalCost !== 0 && React.createElement('div', {
            style: {
                margin: '0 20px 20px 20px',
                fontFamily: 'Menlo, Monaco, "Courier New", monospace',
                fontSize: '0.85em',
                opacity: 0.7
            }
        }, `Total: $${totalCost.toFixed(4)}`)
    )
}