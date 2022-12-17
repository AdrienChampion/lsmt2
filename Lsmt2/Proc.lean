import Lsmt2.Init



namespace Lsmt2.Proc



abbrev Out := IO.Process.Output



abbrev Conf := IO.Process.StdioConfig

namespace Conf
  def piped : Conf :=
    let piped := IO.Process.Stdio.piped
    ⟨piped, piped, piped⟩

  def running : Conf :=
    let piped := IO.Process.Stdio.piped
    let null := IO.Process.Stdio.null
    ⟨null, piped, piped⟩
end Conf



abbrev Handle :=
  IO.Process.Stdio.toHandleType
    IO.Process.Stdio.piped



abbrev Kid := IO.Process.Child
abbrev Kid.Running := Kid Conf.running



abbrev Args := IO.Process.SpawnArgs

namespace Args
  def new (cmd : String) : Args :=
    ⟨Conf.piped, cmd, #[], none, #[]⟩

  variable
    (self : Args)

  def with_arg (arg : String) : Args :=
    { self with args := self.args.push arg }

  def with_args (args : List String) : Args :=
    { self with args := ⟨self.args.data ++ args⟩}

  def run : IO Out :=
    IO.Process.output self
  
  def spawn : IO <| Kid self.toStdioConfig :=
    IO.Process.spawn self
end Args
