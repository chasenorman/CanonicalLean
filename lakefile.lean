import Lake
open Lake DSL

/-- Mirrors the releases of Lean -/
def buildArchive :=
  if System.Platform.isWindows then "windows"
  else if System.Platform.isOSX then
    if System.Platform.target.startsWith "x86_64" then "darwin"
    else "darwin_aarch64"
  else if System.Platform.numBits == 32 then "linux"
  else if System.Platform.target.startsWith "aarch64" then "linux_aarch64"
  else "linux_x86"

package Canonical where
  releaseRepo := "https://github.com/chasenorman/CanonicalLean"
  preferReleaseBuild := true
  buildArchive := buildArchive ++ ".tar.gz"

target canonical pkg : Dynlib := do
  let name := nameToSharedLib "canonical_lean"
  let libPath := pkg.sharedLibDir / name
  let job ← if ← libPath.pathExists then pure (Job.pure ()) else pkg.gitHubRelease.fetch
  job.mapM fun _ => do
    if System.Platform.isWindows then
      let dest := pkg.binDir / name
      unless ← dest.pathExists do
        IO.FS.createDirAll pkg.binDir
        IO.FS.hardLink libPath dest
    return { path := libPath, name := "canonical_lean" }

@[default_target]
lean_lib Canonical where
  precompileModules := true
  moreLinkLibs := #[canonical]

@[test_driver]
lean_lib Test

lean_exe check where
  root := `Check
  supportInterpreter := true
  moreLinkLibs := #[canonical]
