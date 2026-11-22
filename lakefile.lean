import Lake
open Lake DSL

package "swim" where
  version := v!"0.1.0"
  keywords := #["swim", "gossip", "distributed-systems", "formal-verification"]

@[default_target]
lean_lib «SwimCore»

lean_lib «SwimProofs»

lean_exe «swim_sim» where
  root := `SimMain

