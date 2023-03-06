import Lsmt2

open Lsmt2 (Smt)

def script : Smt PUnit := do
  let a := "a"
  let b := "b"
  let c1 := "(= a (* 2 b))"
  let c2 := "(< a (- b 7))"

  IO.println "declaring constants"
  IO.println s! "- {a}"
  IO.println s! "- {b}"

  Smt.declareConst a "Int"
  Smt.declareConst b "Int"

  IO.println "asserting constraints"
  IO.println s! "- {c1}"
  IO.println s! "- {c2}"

  Smt.assert c1
  Smt.assert c2

  IO.println "checksat..."

  if ← Smt.checksat
  then IO.println "sat"
  else IO.println "unsat"

namespace Extensibility
  structure MyState where
    solver : Lsmt2.Solver

  abbrev MyStateM :=
    StateT MyState IO

  instance : MonadLift Smt MyStateM where
    monadLift script := do
      let s ← get
      let (res, solver) ← script s.solver
      set { s with solver }
      pure res
end Extensibility


def main : IO Unit := do
  let solver ← Lsmt2.Solver.mkZ3
  solver.run' script

-- #eval main
