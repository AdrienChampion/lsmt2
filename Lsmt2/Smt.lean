import Lsmt2.Solver
import Lsmt2.Term
import Lsmt2.Parser



namespace Lsmt2



/-! # SMT-LIB 2 Commands -/
namespace Smt.Script
  protected def put (s : String) : Smt PUnit := do
    (← get).stdin.putStr s |> liftM
  protected def putLn (s : String) : Smt PUnit := do
    Script.put s
    Script.put "\n"

  protected def flush : Smt PUnit := do
    (← get).stdin.flush |> liftM
  protected def flushIf : Bool → Smt PUnit
  | true => Script.flush
  | false => pure ()

  protected def putFl (s : String) : Smt PUnit := do
    Script.put s
    Script.flush
  protected def putLnFl (s : String) : Smt PUnit := do
    Script.putLn s
    Script.flush

  protected def readLine : Smt String := do
    (← get).kid.stdout.getLine |> liftM
  
  protected def wexe (w : Writer) : Smt PUnit := do
    let s ← get
    let _ ← w s.stdin

  protected def writeSmt2 [ToSmt2 α] (a : α) : Smt PUnit := do
    ToSmt2.write a |> Script.wexe

  protected def writeArg
    [ToSmt2 Sym] (sym : Sym)
    [ToSmt2 Typ] (typ : Typ)
    (sideWs : Bool := true)
  : Smt PUnit := do
    let (opn, cls) :=
      if sideWs then (" (", ") ") else ("(", ")")
    Script.put opn
    Script.writeSmt2 sym
    Script.put " "
    Script.writeSmt2 typ
    Script.put cls
  
  protected def writeParenArgs
    [ToSmt2 Sym] [ToSmt2 Typ]
    (args : List (Sym × Typ))
  : Smt PUnit := do
    Script.put "("
    loop args
    Script.put ")"
  where
    loop : List (Sym × Typ) → Smt PUnit
    | [] => pure ()
    | (sym, typ) :: tail => do
      Script.writeArg sym typ true
      loop tail

  protected partial def loadSexpr : Smt String := do
    loadSexprAux ""
  where loadSexprAux (s : String) : Smt String := do
    let line ← Script.readLine
    let s := s ++ line
    match Parser.sexpr s.iter with
    | .success _ true =>
      return s
    | .success _ false =>
      loadSexprAux s
    | .error _ e =>
      IO.userError s!"[lsmt2] parser-level error: {e}"
      |> throw

  protected def parse (p : Parsec α) : Smt α := do
    let sexpr ← Script.loadSexpr
    match p sexpr.iter with
    | .success _ res =>
      return res
    | .error _ e =>
      IO.userError s!"[lsmt2] parser-level error: {e}"
      |> throw



  /-! ### Queries
  
  Result-producing SMT-LIB 2 commands.
  -/

  def checksat : Smt Bool := do
    Script.putLnFl "(check-sat)"
    let line ← Script.readLine
    match line.trim with
    | "sat" => pure true
    | "unsat" => pure false
    | line => panic! s!"unexpected checksat answer '{line}'"



  def getModel
    [Parser.Sym σ] [Parser.Typ τ] [Parser.Term α]
  : Smt $ Parser.Model σ τ α := do
    Script.putLnFl "(get-model)"
    Script.parse Parser.getModel

  def getValues
    [Parser.Term σ₁] [Parser.Term σ₂]
    (terms : List τ)
    [ToSmt2 τ]
  : Smt $ Parser.Values σ₁ σ₂ := do
    Script.put "(get-value ("
    terms.foldlM
      (fun _ term => do
        Script.put " "
        Script.writeSmt2 term)
      ()
    Script.putLnFl "))"
    Script.parse Parser.getValues



  /-! ### Commands
  
  SMT-LIB 2 commands producing no result.
  -/

  def assert
    [ToSmt2 α] (term : α)
    (flush : Bool := false)
  : Smt PUnit := do
    Script.put "(assert\n  "
    Script.writeSmt2 term
    Script.putLn "\n)"
    Script.flushIf flush

  def declareFun
    [ToSmt2 Sym] [ToSmt2 Srt]
    (sym : Sym)
    (ins : List (Sym × Srt))
    (typ : Srt)
    (flush : Bool := false)
  : Smt PUnit := do
    let nl := ins.length > 2
    Script.put "(declare-fun "
    Script.writeSmt2 sym
    if nl then Script.put "\n "
    Script.put " "
    Script.writeParenArgs ins
    if nl then Script.put "\n "
    Script.put " "
    Script.writeSmt2 typ
    if nl then Script.put "\n"
    Script.put ")"
    Script.flushIf flush

  def declareConst
    [ToSmt2 Sym] [ToSmt2 Srt]
    (sym : Sym)
    (typ : Srt)
    (flush : Bool := false)
  : Smt PUnit :=
    declareFun sym [] typ flush
end Smt.Script



namespace Smt

  variable
    {Mon : outParam (Type → Type)}
    [Monad Mon]
    [MonadLiftT Smt Mon]

  /-! ### Queries
  
  Result-producing SMT-LIB 2 commands.
  -/

  def checksat : Mon Bool :=
    Script.checksat |> liftM

  def getModel
    [Parser.Sym σ] [Parser.Typ τ] [Parser.Term α]
  : Mon $ Parser.Model σ τ α :=
    Script.getModel |> liftM

  def getValues
    [Parser.Term σ₁] [Parser.Term σ₂]
    (terms : List τ)
    [ToSmt2 τ]
  : Smt $ Parser.Values σ₁ σ₂ :=
    Script.getValues terms |> liftM



  /-! ### Commands
  
  SMT-LIB 2 commands producing no result.
  -/

  def assert
    [ToSmt2 α] (term : α)
    (flush : Bool := false)
  : Mon PUnit :=
    Script.assert term flush |> liftM

  def declareFun
    [ToSmt2 Sym] [ToSmt2 Srt]
    (sym : Sym)
    (ins : List (Sym × Srt))
    (typ : Srt)
    (flush : Bool := false)
  : Mon PUnit :=
    Script.declareFun sym ins typ flush |> liftM

  def declareConst
    [ToSmt2 Sym] [ToSmt2 Srt]
    (sym : Sym)
    (typ : Srt)
    (flush : Bool := false)
  : Mon PUnit :=
    Script.declareConst sym typ flush |> liftM
end Smt
