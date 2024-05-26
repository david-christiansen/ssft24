import Lake
open Lake DSL

require LeanSAT from git "https://github.com/leanprover/leansat.git"@"main"

package «ssft24» {
  precompileModules := true
  -- This package uses a ginormous maximum stack size to avoid
  -- worrying about stack overflows during bitblasting.
  moreGlobalServerArgs := #["--tstack=32000"]
  moreLeanArgs := #["--tstack=32000"]
}

@[default_target]
lean_lib Intro where

@[default_target]
lean_lib Filter where

@[default_target]
lean_exe jsonfilter where
  root := `Main

@[default_target]
lean_lib Imp where
