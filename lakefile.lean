import Lake
open Lake DSL

package «lsmt2» {
  -- add package configuration options here
}

lean_lib «Lsmt2» {
  -- add library configuration options here
}

@[default_target]
lean_exe «lsmt2» {
  root := `Main
}
