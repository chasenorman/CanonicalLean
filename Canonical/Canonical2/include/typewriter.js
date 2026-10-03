import * as React from 'react'
import { useRpcSession, EditorContext, EnvPosContext, InteractiveMessageData } from '@leanprover/infoview'
// InputAbbreviationRewriter comes from include/unicode-input-component.js

const histories = new Map()

const controlStyle = {
  border: 'none',
  font: 'inherit',
  outline: 'inherit',
  marginLeft: '10px',
  padding: '5px 10px',
  borderRadius: '8.5px',
  minWidth: '30px',
  backgroundColor: 'rgb(240, 240, 240)',
  cursor: 'pointer',
  fontSize: '16px'
}

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

function LeanInput({ focused, text, setText, placeholder = "Type here…" }) {
  const editorRef = React.useRef(null)
  const rewriterRef = React.useRef(null)

  // Set up rewriter and DOM → state sync
  React.useEffect(() => {
    const el = editorRef.current
    if (!el) return

    if (focused) el.focus()

    rewriterRef.current = new InputAbbreviationRewriter(
      { abbreviationCharacter: '\\', eagerReplacementEnabled: true },
      el
    )

    const handleInput = () => { setText(el.innerText) }

    el.addEventListener('input', handleInput)

    return () => {
      rewriterRef.current?.resetAbbreviations()
      el.removeEventListener('input', handleInput)
    }
  }, []) // setup only once

  // State → DOM sync
  React.useEffect(() => {
    const el = editorRef.current
    if (!el) return
    if (el.innerText !== text) {
      el.innerText = text
    }
  }, [text])

  return React.createElement(
    'div',
    {
      style: { position: 'relative', width: '100%' }
    },
    [
      React.createElement(
        'span',
        {
          key: 'ph',
          style: {
            position: 'absolute',
            left: 11,
            top: 11,
            opacity: text.trim().length > 0 ? 0 : 0.5,
            pointerEvents: 'none',
            fontFamily: 'Menlo, Monaco, "Courier New", monospace',
            fontSize: '16px',
            whiteSpace: 'pre-wrap'
          }
        },
        placeholder
      ),
      React.createElement('div', {
        key: 'editor',
        ref: editorRef,
        contentEditable: true,
        suppressContentEditableWarning: true,
        role: 'textbox',
        'aria-multiline': 'false',
        style: {
          width: '100%',
          padding: '10px 10px',
          fontSize: '16px',
          borderRadius: '12px',
          border: '1px solid #ccc',
          outline: 'none',
          boxSizing: 'border-box',
          fontFamily: 'Menlo, Monaco, "Courier New", monospace',
          minHeight: '1.8em',
          whiteSpace: 'pre-wrap'
        }
      })
    ]
  )
}

export default function (props) {
  const pos = React.useContext(EnvPosContext)
  const rs = useRpcSession()
  const editorConnection = React.useContext(EditorContext);

  const [name, setName] = React.useState("")
  const [type, setType] = React.useState("")
  const [clear, setClear] = React.useState("")
  const [overrideText, setOverrideText] = React.useState('by ')
  const [err, setErr] = React.useState(props.empty)
  const [term, setTerm] = React.useState('')
  const termRef = React.useRef(null)

  const [hist, setHist] = React.useState(() => {
    if (!histories.has(props.token)) {
      histories.set(props.token, { saves: [props.initial], time: 0 })
    }
    return histories.get(props.token)
  })

  // The history is the single source of truth; the rest of the UI derives from it.
  const save = hist.saves[hist.time]
  const mvars = save.mvars
  const mvar = Math.min(save.selected, mvars.length - 1)
  const success = mvars.length == 0
  const undoEnabled = hist.time > 0
  const redoEnabled = hist.time < hist.saves.length - 1
  const out = success ? props.empty : mvars[mvar].messageData

  function updateHist(next) {
    histories.set(props.token, next)
    setHist(next)
  }

  function pushSave(time, save) {
    updateHist({ saves: [...hist.saves.slice(0, time + 1), save], time: time + 1 })
  }

  function replaceSave(time, save) {
    const saves = hist.saves.slice()
    saves[time] = save
    updateHist({ saves, time })
  }

  // The selection lives in the current save, so undo/redo and remounts restore it.
  function setMvar(index) {
    replaceSave(hist.time, { ...save, selected: index })
  }

  function resetText() {
    setType('')
    setName('')
    setClear('')
    setOverrideText('by ')
    setErr(props.empty)
  }

  // Arriving at a different save resets the inputs and re-renders the term;
  // once no goals remain, the proof is written back into the editor.
  React.useEffect(() => {
    if (success) {
      insert()
    } else {
      resetText()
      refreshTerm()
    }
  }, [save.state])

  // Automate the selected goal in the background; if it succeeds, the automated
  // state replaces the current save. The cleanup cancels the task as soon as the
  // save or the selection changes, making any in-flight result stale.
  React.useEffect(() => {
    if (success) return
    let cancelled = false
    let task = null
    const time = hist.time
    async function automate() {
      task = await rs.call('Canonical2.automateRpc', {
        val: mvars[mvar].mvarId,
        ctx: props.ctx,
        state: save.state
      })
      if (cancelled) { rs.call('Canonical2.cancel', task); return }
      let result = await rs.call('Canonical2.taskGet', {
        task: task,
        ctx: props.ctx,

        selected: mvar,
        expr: props.expr
      })
      task = null
      if (!cancelled && result != 'none' && 'some' in result) {
        replaceSave(time, result.some.val)
      }
    }
    automate()
    return () => {
      cancelled = true
      if (task) { rs.call('Canonical2.cancel', task) }
    }
  }, [save.state, mvar])

  async function refreshTerm() {
    let str = await rs.call('Canonical2.leanStringRpc', {
      val: { expr: props.expr, width: getCols(termRef.current), indent: 0, column: 0, exact: false },
      ctx: props.ctx,
      state: save.state
    })
    setTerm(str)
  }

  async function insert() {
    let str = await rs.call('Canonical2.leanStringRpc', {
      val: { expr: props.expr, width: props.width, indent: props.indent, column: props.column, exact: true },
      ctx: props.ctx,
      state: save.state
    })
    editorConnection.api.applyEdit({
        changes: { [pos.uri]: [{ range: props.range, newText: str }] }
    })
  }

  async function onEnter() {
    if (type.trim().length === 0) return
    let response = await rs.call('Canonical2.addSubgoalRpc', { val: {
      mvarId: mvars[mvar].mvarId,
      name: name.trim().length === 0 ? "h" : name.trim(),
      type: type.trim(),
      clears: clear.trim(),

      selected: mvar,
      expr: props.expr
    }, ctx: props.ctx, state: save.state });
    if ('success' in response) { pushSave(hist.time, response.success.result) }
    else if ('error' in response) { setErr(response.error.msg) }
  }

  function undo() {
    if (hist.time > 0) { updateHist({ ...hist, time: hist.time - 1 }) }
  }
  function redo() {
    if (hist.time < hist.saves.length - 1) { updateHist({ ...hist, time: hist.time + 1 }) }
  }
  function restart() {
    resetText()
    updateHist({ saves: hist.saves.slice(0, 1), time: 0 })
  }
  async function onOverride() {
    if (overrideText.trim().length === 0) return
    let response = await rs.call('Canonical2.overrideRpc', { val: {
      mvarId: mvars[mvar].mvarId,
      term: overrideText,

      selected: mvar,
      expr: props.expr
    }, ctx: props.ctx, state: save.state });
    if ('success' in response) { pushSave(hist.time, response.success.result) }
    else if ('error' in response) { setErr(response.error.msg) }
  }

  return success ?
  React.createElement('p', { style: { color: 'rgb(103, 166, 213)' } }, "Goals accomplished 🎉")
    : 
  React.createElement(
    'div',
    { style: { width: '100%' } },
    React.createElement(
    'div',
      { style: { margin: '8px 0', display: 'flex', flexWrap: 'wrap', rowGap: '1em' } },
      React.createElement(
        'button',
        { style: { ...controlStyle, 
          color: undoEnabled ? 'inherit' : 'rgb(127, 127, 127)',
          cursor: undoEnabled ? 'pointer' : 'default' 
        }, onClick: undo, disabled: !undoEnabled },
        React.createElement(
          'svg',
          {
            style: { verticalAlign: 'middle' },
            width: '19px',
            height: '19px',
            viewBox: '0 0 24 24',
            fill: 'none',
            stroke: 'currentColor',
            strokeWidth: '2',
            strokeLinecap: 'round',
            strokeLinejoin: 'round'
          },
          React.createElement('polyline', { points: '15.5 20 7.5 12 15.5 4' })
        )
      ),

      React.createElement(
        'button',
        { style: { ...controlStyle, 
          color: redoEnabled ? 'inherit' : 'rgb(127, 127, 127)',
          cursor: redoEnabled ? 'pointer' : 'default' 
        }, onClick: redo, disabled: !redoEnabled },
        React.createElement(
          'svg',
          {
            style: { verticalAlign: 'middle' },
            width: '19px',
            height: '19px',
            viewBox: '0 0 24 24',
            fill: 'none',
            stroke: 'currentColor',
            strokeWidth: '2',
            strokeLinecap: 'round',
            strokeLinejoin: 'round'
          },
          React.createElement('polyline', { points: '8.5 20 16.5 12 8.5 4' })
        )
      ),

      React.createElement('button', { style: controlStyle, onClick: restart }, '↻'),
      React.createElement('button', { style: controlStyle, onClick: insert }, 'Insert')
    ),
    React.createElement(
      'div',
      { ref: termRef, style: {
          margin: '8px 0',
          fontFamily: 'Menlo, Monaco, "Courier New", monospace',
          whiteSpace: 'pre-wrap',
          overflow: 'hidden',
        } },
      tokenize(term).map((tok, i) => {
        if (/^\s+$/.test(tok)) {
          return React.createElement('span', { key: i }, tok)
        } else if (tok.startsWith('?')) {
          // Metavariable hole: render the matching select button inline.
          const index = mvars.findIndex(value => value.mvarId === tok.slice(1))
          if (index === -1) return React.createElement('span', { key: i }, tok)
          return React.createElement(
            'label',
            { key: i, style: {
              backgroundColor:
                mvar === index ? 'rgb(35, 122, 255)' : 'rgb(242, 242, 247)',
              color: mvar === index ? 'rgb(204, 228, 255)' : 'rgb(128, 128, 128)',
              borderRadius: '3.5px',
              padding: '0 2px',
              cursor: 'pointer',
            }, },
            React.createElement('input', {
              type: 'radio',
              name: 'mvarGroup',
              checked: mvar === index,
              onChange: () => setMvar(index),
              style: { display: 'none' }
            }),
            '?' + mvars[index].name
          )
        } else if (colorMap[tok]) {
          return React.createElement('span', { key: i, style: { color: colorMap[tok] } }, tok)
        } else {
          return React.createElement('span', { key: i }, tok)
        }
      })
    ),
    React.createElement(InteractiveMessageData, { msg: out }),
    React.createElement(
      'div',
      {
        onKeyDown: e => {
          if (e.key === 'Enter') {
            e.preventDefault();
            onEnter();
          }
        },
        style: {
          display: 'flex',
          flexDirection: 'column',
          gap: '0.5rem',
          width: '100%'
        }
      },

      React.createElement(
        'div',
        {
          style: {
            display: 'flex',
            flexWrap: 'wrap',
            gap: '0.5rem',
            width: '100%',
          }
        },
        React.createElement(
          'div',
          { style: { flex: '4 1 0', minWidth: '360px' } },
          React.createElement(LeanInput, { focused: false, text: type, setText: setType, placeholder: "type" })
        ),
        React.createElement(
          'div',
          { style: { flex: '1 1 0', minWidth: '120px' } },
          React.createElement(LeanInput, { focused: false, text: name, setText: setName, placeholder: "name" })
        )
      ),

      React.createElement(LeanInput, { focused: false, text: clear, setText: setClear, placeholder: "clear" })
    ),
    React.createElement('div', {
        onKeyDown: e => {
          if (e.key === 'Enter') {
            e.preventDefault();
            onOverride();
          }
        },
        style: { padding: '50px 0 10px 0', width: '100%' }
      },
      React.createElement(LeanInput, { focused: false, text: overrideText, setText: setOverrideText, placeholder: "override" })
    ),
    React.createElement(
      'div',
      { style: { color: "red" } },
      React.createElement(InteractiveMessageData, { msg: err })
    ),
  )
}