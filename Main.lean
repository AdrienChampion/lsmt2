import Lsmt2

open Lsmt2.Smt in
open Lsmt2.Io in
def script : Lsmt2.ScriptU Id := do
  let a := "a"
  let b := "b"
  let c1 := "(= a (* 2 b))"
  let c2 := "(< a (- b 7))"

  println "declaring constants"
  println s! "- {a}"
  println s! "- {b}"

  declareConst a "Int"
  declareConst b "Int"

  println "asserting constraints"
  println s! "- {c1}"
  println s! "- {c2}"

  assert c1
  assert c2

  println "checksat..."

  if ← checksat
  then println "sat"
  else println "unsat"

def main : IO Unit := do
  let solver ← Lsmt2.Solver.mkZ3
  solver.runToIO script

#eval main
