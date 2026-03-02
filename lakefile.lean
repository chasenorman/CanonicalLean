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
  preferReleaseBuild := true
  buildArchive := buildArchive ++ ".tar.gz"

target canonical pkg : Dynlib := do
  let libPath := pkg.sharedLibDir / nameToSharedLib "canonical_lean"
  if !(← libPath.pathExists) then
    logWarning "Canonical dynlib fallback used!"
    let archiveName := buildArchive ++ ".tar.gz"
    let url := s!"https://github.com/chasenorman/CanonicalLean/releases/download/v{Lean.versionString}/{archiveName}"
    let archivePath := pkg.buildDir / archiveName
    let curl ← IO.Process.output {
      cmd := "curl", args := #["-fsSL", "-o", archivePath.toString, url]
    }
    if curl.exitCode != 0 then
      error s!"Failed to download {url}:\n{curl.stderr}"
    IO.FS.createDirAll pkg.buildDir
    let tar ← IO.Process.output {
      cmd := "tar", args := #["-xzf", archivePath.toString, "-C", pkg.buildDir.toString]
    }
    if tar.exitCode != 0 then
      error s!"Failed to extract {archivePath}:\n{tar.stderr}"
  return Job.pure { path := libPath, name := "canonical_lean" }

@[default_target]
lean_lib Canonical where
  precompileModules := true
  moreLinkLibs := #[canonical]

@[test_driver]
lean_lib Test
