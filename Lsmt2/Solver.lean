import Lsmt2.Init
import Lsmt2.Proc
import Lsmt2.Term



namespace Lsmt2



structure Solver.Conf where
  cmd : String
  args : List String

namespace Solver.Conf
  def z3 : Solver.Conf where
    cmd := "z3"
    args := ["-smt2", "-in"]

  def toProcArgs
    (self : Solver.Conf)
  : Proc.Args :=
    Proc.Args.new self.cmd
    |>.with_args self.args
end Solver.Conf



structure Solver where
private innerMk ::
  kid : Proc.Kid.Running
  stdin : Proc.Handle
  conf : Solver.Conf
  depth : Nat

namespace Solver
  def mk (conf : Solver.Conf) : IO Solver := do
    let args := conf.toProcArgs
    let kid ← args.spawn
    let (stdin, kid) ← kid.takeStdin

    pure ⟨kid, stdin, conf, 0⟩

  def mkZ3 : IO Solver :=
    mk Solver.Conf.z3

  def stdout
    (self : Solver)
  : IO.FS.Handle :=
    self.kid.stdout
end Solver



section Transformer

  namespace Script
    abbrev Result :=
      EStateM.Result

    abbrev ResultT (mon : Type → Type u) (α : Type) :=
      mon (Result Error (Solver × IO.RealWorld) α)
  end Script

  abbrev Script (mon : Type → Type u) (α : Type) :=
    Solver → IO.RealWorld → Script.ResultT mon α

  abbrev ScriptU (mon : Type → Type u) :=
    Script mon PUnit



  variable
    {mon : outParam (Type → Type u)}
    [Mon : Monad mon]



  namespace Script
    def context
      (script : Script mon α)
      (ctx : χ)
      [i : IntoErrorCtx χ]
    : Script mon α
    | s, io =>
      Mon.bind
        (script s io)
        fun
        | .ok a state =>
          .ok a state
          |> Mon.pure
        | .error e state =>
          let e := i.into ctx |> e.context'
          .error e state
          |> Mon.pure

    def pure (a : α) : Script mon α
    | s, io => .ok a (s, io) |> Mon.pure

    def tryCatch
      (a? : Script mon α)
      (errAction : Error → Script mon α)
    : Script mon α
    | s, io =>
      Mon.bind
        (a? s io)
        fun
        | .ok a s => .ok a s |> Mon.pure
        | .error e (s, io) => errAction e s io

    def throw (e : Error) : Script mon α
    | s, io => .error e (s, io) |> Mon.pure
    
    def map (a? : Script mon α) (f : α → β) : Script mon β
    | s, io => do
      Mon.bind
        (a? s io)
        fun
        | .ok a (s, io) => pure (f a) s io
        | .error e (s, io) => throw e s io
    
    def seq (f? : Script mon <| α → β) (getA? : Unit → Script mon α) : Script mon β
    | s, io =>
      let f? := f? s io
      Mon.bind
        f?
        (fun
        | .ok f (s, io) =>
          let a? := getA? () s io
          Mon.map
            (fun
            | .ok a s => .ok (f a) s
            | .error e s => .error e s)
            a?
        | .error e s => .error e s |> Mon.pure)
      
    def bind (a? : Script mon α) (b?Ofa : α → Script mon β) : Script mon β
    | s, io =>
      let a? := a? s io
      Mon.bind
        a?
        fun
        | .ok a (s, io) => b?Ofa a s io
        | .error e (s, io) => throw e s io
  end Script



  instance instMonadScript
  : Monad <| Script mon where
    pure := Script.pure
    bind := Script.bind

  instance instMonadExceptScript : MonadExcept Error <| Script mon where
    throw err :=
      Script.throw err
    tryCatch res errorAction :=
      Script.tryCatch res errorAction

  instance instResExtScript : ResExt (Script mon α) (Script mon α) where
    context := Script.context


  instance : MonadLift mon (Script mon) where
    monadLift m s io :=
      Mon.map (.ok · (s, io)) m
  
  instance : MonadLift IO (Script mon) where
    monadLift m s io :=
      match m io with
      | .ok a io => Script.pure a s io
      | .error e io => Script.throw e s io
end Transformer



namespace Solver
  variable
    {mon : Type → Type v}
    [Mon : Monad mon]
    (self : Solver)
    (prog : Script mon α)
    (io : Io)

  def run : Script.ResultT mon α :=
    prog self io

  def run' : ResT mon α :=
    Mon.bind
      (self.run prog io)
      fun 
      | .ok a _ => .ok a |> pure
      | .error e _ => .error e |> pure

  def runToIO (prog : Script Id α) : IO PUnit
  | io =>
    match self.run prog io with
    | .ok _ (_, io) =>
      EStateM.Result.ok () io
    | .error e (_, io) =>
      EStateM.Result.error e.toIO io
    
end Solver
