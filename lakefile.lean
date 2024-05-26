import Lake
open Lake DSL

require LeanSAT from git "https://github.com/leanprover/leansat.git"@"main"

package «ssft24» {
  precompileModules := true
}

@[default_target]
lean_lib Intro where

@[default_target]
lean_lib Filter where

@[default_target]
lean_exe jsonfilter where
  root := `Main
