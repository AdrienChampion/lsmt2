/-! # Basic Definitions -/



def String.lines
  (s : String)
: List String :=
  s.split fun c => c = '\n' ∨ c = '\r'



namespace Lsmt2



export IO (println)



/-- `𝕂`onstant combinator. -/
def 𝕂 (val : α) : β → α :=
  fun _ => val



abbrev IOu := IO Unit
abbrev Io : Type := IO.RealWorld
