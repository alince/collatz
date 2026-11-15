import Lake
open Lake DSL

package «collatz_formal» where
  moreLeanArgs := #["-M", "2048", "-T", "200000", "-j", "2"]

@[default_target]
lean_lib «CollatzFormal» where
  roots := #[`CollatzFormal]
