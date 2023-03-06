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



abbrev Smt (α : Type) :=
  StateT Solver IO α



namespace Solver
  variable
    (self : Solver)
    (prog : Smt α)

  def run : IO (α × Solver) :=
    prog self

  def run' : IO α :=
    Prod.fst <$> prog self
end Solver
