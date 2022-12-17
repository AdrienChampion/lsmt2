/-! # Writer/Reader Helpers -/

namespace Lsmt2



section Writer
  abbrev Writer :=
    StateT IO.FS.Handle IO Unit

  namespace Writer
    def pushStr (s : String) : Writer := do
      let w ← get
      w.putStr s
    
    def pushStrLn (s : String) : Writer := do
      let w ← get
      w.putStrLn s
    
    def flush : Writer := do
      let w ← get
      w.flush

    def pushStrFl (s : String) : Writer := do
      pushStr s
      flush

    def pushStrLnFl (s : String) : Writer := do
      pushStrLn s
      flush
  end Writer
end Writer



section Reader
  abbrev Reader (α : Type) :=
    StateT IO.FS.Handle IO α

  namespace Reader
    def throw (s : String) : IO α :=
      let e : IO.Error := IO.Error.userError s
      EStateM.throw e

    protected partial def loadSexpr.aux
      (oparen : Nat)
      (s : String)
      (input : IO.FS.Handle)
    : Reader String := do
      let mut oparen := oparen
      let line ← input.getLine
      if line.isEmpty then
        throw "reached EOI"
      else
        for c in line.data do
          match c with
          | '(' => oparen := oparen + 1
          | ')' =>
            match oparen with
            | 0 => throw "paren mismatch"
            | count + 1 => oparen := count
          | _ => pure ()
        return s ++ line

    partial def loadSexpr : Reader String := do
      let input ← get
      loadSexpr.aux 0 "" input
  end Reader
end Reader