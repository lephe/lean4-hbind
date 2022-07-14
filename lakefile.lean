import Lake
open Lake DSL

package hbind {
  -- add package configuration options here
}

lean_lib HBind {
  -- add library configuration options here
}

@[defaultTarget]
lean_exe hbind {
  root := `Main
}
