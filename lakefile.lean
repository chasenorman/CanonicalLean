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
  let libPath := pkg.sharedLibDir / nameToSharedLib "canonical_lean"
  let lib := { path := libPath, name := "canonical_lean" }
  if !(← libPath.pathExists) then
    (← pkg.gitHubRelease.fetch).mapM (fun _ => do pure lib)
  else return Job.pure lib

@[default_target]
lean_lib Canonical where
  precompileModules := true
  moreLinkLibs := #[canonical]

@[test_driver]
lean_lib Test

/--
`libcanonical_lean` is linked against `libleanshared`, so executables must use that same Lean runtime
rather than Lake's default static one (two runtimes in one process segfault). Listing it before Lake's
static `-lInit -lLean -lleanrt ...` makes the linker resolve every Lean symbol from the shared library.
-/
def sharedLeanLinkArgs : Array String := #["-lleanshared"]

lean_exe robustness where
  root := `Canonical.Test.Robustness
  supportInterpreter := true
  moreLinkLibs := #[canonical]
  moreLinkArgs := sharedLeanLinkArgs

lean_exe debug where
  root := `Canonical.Test.Debug
  supportInterpreter := true
  moreLinkLibs := #[canonical]
  moreLinkArgs := sharedLeanLinkArgs
