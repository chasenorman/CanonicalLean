import * as React from 'react';
import { useRpcSession, EditorContext, EnvPosContext } from '@leanprover/infoview';
export default function(props) {
    const pos = React.useContext(EnvPosContext)
    const iframeRef = React.useRef(null);
    const editorConnection = React.useContext(EditorContext);

    React.useEffect(() => {
    const sendTheme = () => {
        const style = getComputedStyle(document.documentElement);
        const vars = {
        text: style.getPropertyValue('--vscode-foreground'),
        metaBackground: style.getPropertyValue('--vscode-list-hoverBackground'),
        listBackground: style.getPropertyValue('--vscode-list-hoverBackground'),
        optionBackground: style.getPropertyValue('--vscode-list-hoverBackground'),
        listHover: style.getPropertyValue('--vscode-inputOption-activeBackground'),
        listBorder: style.getPropertyValue('--vscode-input-border'),
        };
        const isDark = document.body.classList.contains('vscode-dark');
        iframeRef.current?.contentWindow?.postMessage({ type: 'theme', vars, isDark: isDark }, '*');
    };

    const iframe = iframeRef.current;
    iframe?.addEventListener('load', sendTheme);
    return () => iframe?.removeEventListener('load', sendTheme);
    }, []);

    const rs = useRpcSession();
    React.useEffect(() => {
    const onMessage = async (event) => {
        if (event.data?.type === 'insert') {
            const result = await rs.call('getRefinementStr', { pos: props.pos, rpcData: props.rpcData, range: props.range });
            editorConnection.api.applyEdit({
                changes: { [pos.uri]: [{ range: props.range, newText: result }] }
            })
        }
    };
    window.addEventListener('message', onMessage);
    return () => window.removeEventListener('message', onMessage);
    }, []);

    return React.createElement('iframe', {
    ref: iframeRef,
    src: 'http://localhost:3000',
    width: '100%',
    height: '500px',
    style: { border: 'none', margin: 0 }
    });
}