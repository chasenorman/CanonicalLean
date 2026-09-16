import * as React from 'react'
import { useRpcSession, InteractiveMessageData } from '@leanprover/infoview'

const h = React.createElement

export default function (props) {
    const rs = useRpcSession()
    const [suggestions, setSuggestions] = React.useState(null)
    const [status, setStatus] = React.useState('')
    const [progress, setProgress] = React.useState('')

    React.useEffect(() => {
        rs.call('Canonical2.getSuggestions', props.task)
            .then(setSuggestions, e => setStatus(String(e.message || e)))
        let stopped = false
        async function recvLoop() {
            while (!stopped) {
                const msg = await rs.call('Canonical2.recv', props.pipe)
                if ('status' in msg) setStatus(msg.status)
                if ('progress' in msg) setProgress(msg.progress)
            }
        }
        recvLoop()
        return () => { stopped = true }
    }, [])

    if (suggestions === null) {
        return h('div', { style: { margin: '20px' } },
            h('div', null, status || 'Selecting premises…'),
            progress !== '' && h('div', { style: { height: '4px', marginTop: '8px',
                backgroundColor: 'rgba(128, 128, 128, 0.2)' } },
                h('div', { style: { width: `${progress}%`, height: '100%', backgroundColor: 'currentColor' } })))
    }

    return h('div', { style: { margin: '20px' } },
        suggestions.length === 0 && 'No suggestions.',
        suggestions.map((s, i) => h('div', { key: i },
            h(InteractiveMessageData, { msg: s.decl }),
            h('span', { style: { opacity: 0.5, marginLeft: '12px' } }, s.score.toFixed(2)))))
}
