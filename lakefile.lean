import Lake
open Lake DSL

require LeanSAT from git "https://github.com/leanprover/leansat.git"

package «ssft24» where
  -- add package configuration options here
  moreGlobalServerArgs := #["--tstack=32000"]

lean_lib Imp2 where
