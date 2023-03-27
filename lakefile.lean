import Lake
open Lake DSL

package «lsmt2» {
  -- add package configuration options here
}

lean_lib «Lsmt2» {
  -- add library configuration options here
}

meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

@[default_target]
lean_exe «lsmt2» {
  root := `Main
}
