import Lake
open Lake DSL

require LeanSAT from git "https://github.com/leanprover/leansat.git"@"main"

package «ssft24» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--tstack=32000"]

lean_lib Filter where
  -- add library configuration options here

@[default_target]
lean_exe jsonfilter where
  root := `Main


lean_lib Imp where
