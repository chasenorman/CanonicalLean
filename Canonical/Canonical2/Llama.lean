module

import Canonical.Canonical2.Util
public import Lake.Build.Trace
public import Lake.Util.Lift
public import Lake.Config.Defaults
public import Lake.Util.Git
public import Lake.Load.Manifest

public section

open Lean System

namespace Canonical2

variable (log : String → String → IO Unit)

def daemonHost : String := "127.0.0.1"
def daemonPort : Nat := 8765
def premisePort : Nat := 8766

private def llamaCppRepo : String := "FrederickPu/llama.cpp"
private def llamaCppTag : String := "premise-v9"
def mathlibCache : String := "chasenorman/mathlib-cache"

private def runCommand (cmd : String) (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd, args }
  if out.exitCode ≠ 0 then
    throw <| IO.userError s!"`{cmd}` failed ({out.exitCode}):\n{out.stderr}"
  return out.stdout

private partial def findFileNamed (root : FilePath) (name : String) : IO (Option FilePath) := do
  for entry in ← root.readDir do
    if entry.fileName == name then return some entry.path
    if ← entry.path.isDir then
      if let some path ← findFileNamed entry.path name then return some path
  return none

private def platformSuffix : String :=
  if System.Platform.isWindows then
    if System.Platform.target.startsWith "aarch64" then "bin-win-cpu-arm64.zip"
    else "bin-win-vulkan-x64.zip"
  else if System.Platform.isOSX then
    if System.Platform.target.startsWith "x86_64" then "bin-macos-x64.tar.gz"
    else "bin-macos-arm64.tar.gz"
  else if System.Platform.target.startsWith "aarch64" then "bin-ubuntu-vulkan-arm64.tar.gz"
  else "bin-ubuntu-vulkan-x64.tar.gz"

private def readProgress (h : IO.FS.Handle) : IO Unit := do
  let mut buf := ""
  while true do
    let chunk ← h.read 256
    if chunk.size = 0 then break
    let parts := (buf ++ String.fromUTF8! chunk).splitOn "\r"
    for p in parts.dropLast do
      if let some n := (p.dropWhile (· = ' ')).takeWhile (· ≠ ' ') |>.toNat? then
        log "progress" (toString n)
    buf := parts.getLastD ""

private def downloadWithProgress (url : String) (dest : FilePath)
    (what : String := dest.fileName.getD dest.toString) : IO Unit := do
  let dir := dest.parent.getD "."
  let part : FilePath := ⟨dest.toString ++ ".part"⟩
  log "status" s!"Downloading {what} to {dir}:"
  let size? : IO (Option UInt64) := do
    try return some (← part.metadata).byteSize catch _ => return none
  let mut last ← size?
  let mut stalled := 5
  while (← part.pathExists) && stalled < 10 do
    IO.sleep 1000
    let now ← size?
    stalled := if now == last then stalled + 1 else 0
    last := now
  if !(← part.pathExists) && (← dest.pathExists) then return
  IO.FS.createDirAll dir
  let child ← IO.Process.spawn {
    cmd := "curl"
    args := #["-fL", "--progress-meter", "--retry", "3", "-C", "-", "-o", part.toString, url]
    stdin := .null
    stdout := .null
    stderr := .piped
  }
  readProgress log child.stderr
  if (← child.wait) ≠ 0 then throw <| IO.userError s!"curl failed: {url}"
  IO.FS.rename part dest
  log "progress" ""
  log "status" ""

private def unpack (archive root : FilePath) : IO Unit := do
  if System.Platform.isWindows then
    let sysRoot := (← IO.getEnv "SystemRoot").getD "C:\\Windows"
    let tar := System.FilePath.mk sysRoot / "System32" / "tar.exe"
    let _ ← runCommand tar.toString #["-xf", archive.toString, "-C", root.toString]
  else
    let _ ← runCommand "tar" #["-xf", archive.toString, "-C", root.toString]

private def ensureLlama : IO FilePath := do
  let root := (← cacheDir) / "llama.cpp" / "release" / llamaCppTag
  let exeName := if System.Platform.isWindows then "llama-server.exe" else "llama-server"
  if ← root.pathExists then
    if let some exe ← findFileNamed root exeName then return exe
  let fileName := s!"llama-{llamaCppTag}-{platformSuffix}"
  let archive := root / fileName
  downloadWithProgress log s!"https://github.com/{llamaCppRepo}/releases/download/{llamaCppTag}/{fileName}"
    archive
  unpack archive root
  IO.FS.removeFile archive
  let some exe ← findFileNamed root exeName |
    throw <| IO.userError s!"{fileName} did not contain {exeName}"
  return exe

private def ensureModelFile (repo filename : String) : IO System.FilePath := do
  let dest := (← cacheDir) / repo / filename
  unless ← dest.pathExists do
    downloadWithProgress log s!"https://huggingface.co/{repo}/resolve/main/{filename}" dest (what := "model")
  return dest

private def isPortHealthy (port : Nat) : IO Bool := do
  return (← IO.Process.output { cmd := "curl", args := #["-sSf", "--max-time", "1",
    s!"http://{daemonHost}:{port}/health"] }).exitCode = 0

private def powershellLiteral (value : String) : String :=
  "'" ++ value.replace "'" "''" ++ "'"

/-- Unix: `nohup` sets SIGHUP=ignore in the child before exec.
Windows: PowerShell's `Start-Process` detaches the server from Lean. -/
def spawnDaemon (serverArgs : Array String) (port : Nat) : IO Unit := do
  let server ← ensureLlama log
  let cwd := server.parent.getD "."
  let (cmd, args) := if System.Platform.isWindows then
    let quotedArgs := serverArgs.map fun arg => powershellLiteral ("\"" ++ arg ++ "\"")
    let command := s!"Start-Process -FilePath {powershellLiteral server.toString} " ++
      s!"-ArgumentList @({String.intercalate "," quotedArgs.toList}) " ++
      s!"-WorkingDirectory {powershellLiteral cwd.toString} -WindowStyle Hidden"
    ("powershell.exe", #["-NoProfile", "-NonInteractive", "-Command", command])
  else
    ("nohup", #[server.toString] ++ serverArgs)
  let launcher ← IO.Process.spawn {
    cmd, args, cwd := cwd.toString
    stdin := .null, stdout := .null, stderr := .null
  }
  for _ in [:240] do
    if ← isPortHealthy port then return
    if let some code ← launcher.tryWait then
      if code ≠ 0 then throw <| IO.userError s!"{cmd} exited during startup ({code})"
    IO.sleep 500
  throw <| IO.userError s!"{server} did not come up within 120s"

structure HfRef where
  name : String
  deriving FromJson

structure HfRefs where
  branches : Array HfRef
  deriving FromJson

def killDaemon (port : Nat) : IO Unit := do
  if System.Platform.isWindows then
    let _ ← IO.Process.output { cmd := "powershell.exe", args := #["-NoProfile", "-NonInteractive", "-Command",
      s!"Get-NetTCPConnection -LocalPort {port} -State Listen -ErrorAction SilentlyContinue | ForEach-Object \{ Stop-Process -Id $_.OwningProcess -Force }"] }
  else
    let out ← IO.Process.output { cmd := "lsof", args := #["-ti", s!"tcp:{port}", "-sTCP:LISTEN"] }
    for pid in out.stdout.splitOn "\n" do
      unless pid.trimAscii.isEmpty do
        let _ ← IO.Process.output { cmd := "kill", args := #[pid.trimAscii.toString] }
  for _ in [:40] do
    unless ← isPortHealthy port do return
    IO.sleep 250

def cacheRelease : String := "v" ++ Lean.versionString
def cacheUrl (file : String) : String :=
  s!"https://huggingface.co/datasets/{mathlibCache}/resolve/{cacheRelease}/{file}"

/-- Whether the dataset has `file` for this Lean version (`false` offline too). -/
def cacheAvailable (file : String) : IO Bool := do
  return (← IO.Process.output { cmd := "curl", args := #["-sIfL", "--max-time", "5", cacheUrl file] }).exitCode = 0

/-- Download the dataset's `file` for this Lean version over `db`, if the dataset
has it. A running daemon is stopped first so it respawns on the new database. -/
private def downloadCache (db : FilePath) (file : String) : IO Bool := do
  unless ← cacheAvailable file do return false
  killDaemon premisePort
  for suffix in ["-wal", "-shm"] do
    try IO.FS.removeFile ⟨db.toString ++ suffix⟩ catch _ => pure ()
  downloadWithProgress log (cacheUrl file) db (what := s!"{file} for Lean {cacheRelease}")
  return true

/-- With Mathlib installed, keep `db` at this version's Mathlib cache
(`<db>.version` records which version is installed). Otherwise seed a missing
`db` with Lean's own cache. -/
private def ensureCache (db : FilePath) : IO Unit := do
  if ← (do let _ ← findOLean `Mathlib; pure true) <|> pure false then
    let marker : FilePath := ⟨db.toString ++ ".version"⟩
    let installed ← try pure (← IO.FS.readFile marker).trimAscii.toString catch _ => pure ""
    if installed == cacheRelease && (← db.pathExists) then return
    if ← downloadCache log db "premise.db" then IO.FS.writeFile marker s!"{cacheRelease}\n"
  else if !(← db.pathExists) then
    let _ ← downloadCache log db "lean.db"

def startPremiseDaemon (prebuilt := true) : IO Unit := do
  let libDir := (← IO.currentDir) / ".lake" / "build" / "lib" / "lean"
  IO.FS.createDirAll libDir
  if prebuilt then ensureCache log (libDir / "premise.db")
  if ← isPortHealthy premisePort then return
  let model ← ensureModelFile log "chasenorman/lean-premise-distilroberta-GGUF"
    "thomas-zhu-lean-premise.f16.gguf"
  let args := #["--premise", "-m", model.toString,
    "--host", daemonHost, "--port", toString premisePort, "--pooling", "mean",
    "--ctx-size", "512", "--index-db", (libDir / "premise.db").toString]
  log "status" "Starting premise server…"
  spawnDaemon log args premisePort
  log "status" ""

def startSubgoalDaemon : IO Unit := do
  if ← isPortHealthy daemonPort then return
  let model ← ensureModelFile log "awhecmu/canonical-drafter-ei2m-drafter-GGUF"
    "ei2m-drafter-Q5_K_M.gguf"
  spawnDaemon log #["-m", model.toString, "--host", daemonHost,
    "--port", toString daemonPort,
    "--n-gpu-layers", "-1", "--mlock", "--ctx-size", "8192",
    -- The SFT drafter is non-thinking; disable reasoning at the server level too,
    -- since the model may still open a think block after a tool-error turn.
    "--reasoning-budget", "0",
    "--parallel", "1", "--cache-ram", "0", "--sleep-idle-seconds", "1800"] daemonPort
