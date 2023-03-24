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



abbrev SmtT (μ : Type → Type) [MonadLiftT IO μ] (α : Type) :=
  StateT Solver μ α

abbrev Smt (α : Type) :=
  StateT Solver IO α



instance instMonadLiftIOSmtT
  [Lift : MonadLiftT IO μ] [Monad μ]
: MonadLift IO (SmtT μ) where
  monadLift io state :=
    Lift.monadLift io
    >>= fun res => pure (res, state)

instance instMonadLiftSmtSmtT
  [MonadLiftT IO μ] [Monad μ]
: MonadLift Smt (SmtT μ) where
  monadLift smt state := do
    let (a, state) ← smt state
    return (a, state)



namespace Solver
  variable
    (self : Solver)
    [Monad μ]
    [MonadLiftT IO μ]
    (prog : SmtT μ α)

  def run : μ $ α × Solver :=
    prog self

  def run' : μ α :=
    Prod.fst <$> prog self
end Solver
