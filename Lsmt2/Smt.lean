import Lsmt2.Solver
import Lsmt2.Term
import Lsmt2.Parser



namespace Lsmt2



variable
  {mon : Type → Type u}
  [Mon : Monad mon]



/-! # IO Interactions in a Solver Monad -/
namespace Io
  def println (msg : String) : Script mon PUnit := do
    IO.println msg |> liftM

  def print (msg : String) : Script mon PUnit := do
    IO.print msg |> liftM

  def eprintln (msg : String) : Script mon PUnit := do
    IO.eprintln msg |> liftM

  def eprint (msg : String) : Script mon PUnit := do
    IO.eprint msg |> liftM
end Io



private def get : Script mon Solver
| s => Script.pure s s
private def set (s: Solver) : Script mon PUnit
| _ => Script.pure () s
private def getIO : Script mon Io
| s, io => Script.pure io s io
private def setIO (io : Io) : Script mon PUnit
| s, _ => Script.pure () s io



/-! # SMT-LIB 2 Commands -/
namespace Smt
  protected def put (s : String) : Script mon PUnit := do
    (← get).stdin.putStr s |> liftM
  protected def putLn (s : String) : Script mon PUnit := do
    Smt.put s
    Smt.put "\n"

  protected def flush : Script mon PUnit := do
    (← get).stdin.flush |> liftM
  protected def flushIf : Bool → Script mon PUnit
  | true => Smt.flush
  | false => pure ()

  protected def putFl (s : String) : Script mon PUnit := do
    Smt.put s
    Smt.flush
  protected def putLnFl (s : String) : Script mon PUnit := do
    Smt.putLn s
    Smt.flush

  protected def readLine : Script mon String := do
    (← get).kid.stdout.getLine |> liftM
  
  protected def wexe (w : Writer) : Script mon PUnit
  | s, io =>
    match w s.stdin io with
    | .ok _ io => Script.pure () s io
    | .error e io => Script.throw e s io

  protected def writeSmt2 [ToSmt2 α] (a : α) : Script mon PUnit := do
    ToSmt2.write a |> Smt.wexe

  protected def writeArg
    [ToSmt2 Sym] (sym : Sym)
    [ToSmt2 Typ] (typ : Typ)
    (sideWs : Bool := true)
  : ScriptU mon := do
    let (opn, cls) :=
      if sideWs then (" (", ") ") else ("(", ")")
    Smt.put opn
    Smt.writeSmt2 sym
    Smt.put " "
    Smt.writeSmt2 typ
    Smt.put cls
  
  protected def writeParenArgs
    [ToSmt2 Sym] [ToSmt2 Typ]
    (args : List (Sym × Typ))
  : ScriptU mon := do
    Smt.put "("
    loop args
    Smt.put ")"
  where
    loop : List (Sym × Typ) → ScriptU mon
    | [] => pure ()
    | (sym, typ) :: tail => do
      Smt.writeArg sym typ true
      loop tail

  protected partial def loadSexpr : Script mon String := do
    loadSexprAux ""
  where loadSexprAux (s : String) : Script mon String := do
    let line ← Smt.readLine
    let s := s ++ line
    match Parser.sexpr s.iter with
    | .success _ true =>
      return s
    | .success _ false =>
      loadSexprAux s
    | .error _ e =>
      Error.msg e
      |>.context' "parser-level error"
      |> throw

  protected def parse (p : Parsec α) : Script mon α := do
    let sexpr ← Smt.loadSexpr
    Io.println s!"sexpr: `{sexpr}`"
    match p sexpr.iter with
    | .success _ res =>
      return res
    | .error _ e =>
      Error.msg e
      |>.context' "parser-level error"
      |> throw



  /-! ### Queries
  
  Result-producing SMT-LIB 2 commands.
  -/

  def checksat : Script mon Bool :=
    checksat'.context "during check-sat"
  where checksat' := do
    Smt.putLnFl "(check-sat)"
    let line ← Smt.readLine
    match line.trim with
    | "sat" => pure true
    | "unsat" => pure false
    | _ => panic! s!"unexpected checksat answer '{line}'"



  def getModel
    [Parser.Sym σ] [ToString σ] [Parser.Typ τ] [Parser.Term α]
  : Script mon <| Parser.Model σ τ α :=
    getModel'.context "during get-model"
  where
    getModel' := do
      Smt.putLnFl "(get-model)"
      Smt.parse Parser.getModel



  def getValues
    [Parser.Term σ₁] [Parser.Term σ₂]
    (terms : List τ)
    [ToSmt2 τ]
  : Script mon <| Parser.Values σ₁ σ₂ :=
    getValues'.context "during get-value"
  where
    getValues' : Script mon <| Parser.Values σ₁ σ₂ := do
      Smt.put "(get-value ("
      terms.foldlM
        (fun _ term => do
          Smt.put " "
          Smt.writeSmt2 term)
        ()
      Smt.putLnFl "))"
      Smt.parse Parser.getValues



  /-! ### Commands
  
  SMT-LIB 2 commands producing no result.
  -/

  def assert
    [ToSmt2 α] (term : α)
    (flush : Bool := false)
  : ScriptU mon :=
    assert'.context "during assert"
  where assert' := do
    Smt.put "(assert\n  "
    Smt.writeSmt2 term
    Smt.putLn "\n)"
    Smt.flushIf flush

  def declareFun
    [ToSmt2 Sym] [ToSmt2 Srt]
    (sym : Sym)
    (ins : List (Sym × Srt))
    (typ : Srt)
    (flush : Bool := false)
  : ScriptU mon :=
    declareFun'.context "during declare-fun"
  where declareFun' := do
    let nl := ins.length > 2
    Smt.put "(declare-fun "
    Smt.writeSmt2 sym
    if nl then Smt.put "\n "
    Smt.put " "
    Smt.writeParenArgs ins
    if nl then Smt.put "\n "
    Smt.put " "
    Smt.writeSmt2 typ
    if nl then Smt.put "\n"
    Smt.put ")"
    Smt.flushIf flush

  def declareConst
    [ToSmt2 Sym] [ToSmt2 Srt]
    (sym : Sym)
    (typ : Srt)
    (flush : Bool := false)
  : ScriptU mon :=
    declareFun.declareFun' sym [] typ flush
    |>.context "during declare-const"
end Smt
