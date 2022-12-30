import Lsmt2.Smt



namespace Lsmt2.Example



open Lean.Parsec



structure Symbol where
  sym : String

namespace Symbol
  protected def toString : Symbol → String :=
    Symbol.sym

  def parse : Parsec Symbol := do
    let ident ← Parser.Ident.parse
    return ⟨toString ident⟩
end Symbol

instance instParserSymSymbol : Parser.Sym Symbol :=
  ⟨Symbol.parse⟩
instance instToStringSymbol : ToString Symbol :=
  ⟨Symbol.toString⟩
instance instToSmt2Symbol : ToSmt2 Symbol :=
  ⟨Writer.pushStr ∘ Symbol.sym⟩



inductive Typ
| Int
| Boo

namespace Typ
  protected def toString : Typ → String
    | Int => "Int"
    | Boo => "Bool"

  def toSmt2 : Typ → Writer :=
    Writer.pushStr ∘ Typ.toString

  def parse : Parsec Typ := do
    𝕂 Typ.Int <$> pstring "Int"
    <|> 𝕂 Typ.Boo <$> pstring "Bool"
end Typ

instance instParserTypTyp : Parser.Typ Typ :=
  ⟨Typ.parse⟩
instance instToStringTyp : ToString Typ :=
  ⟨Typ.toString⟩
instance instToSmt2Typ : ToSmt2 Typ :=
  ⟨Typ.toSmt2⟩



inductive Const
| I : Int → Const
| B : Bool → Const

namespace Const
  def nat : Nat → Const :=
    Const.I ∘ Int.ofNat
  def int : Int → Const :=
    Const.I
  def bool : Bool → Const :=
    Const.B

  protected def toString : Const → String
    | I i => toString i
    | B b => toString b

  protected def toSmt2 : Const → Writer
    | I (Int.ofNat n) =>
      toString n |> Writer.pushStr
    | I (Int.negSucc n) => do
      Writer.pushStr "(- "
      n + 1 |> toString |> Writer.pushStr
      Writer.pushStr ")"
    | B b =>
      toString b |> Writer.pushStr

  def parse : Parsec Const := do
    int <|> bool
  where
    int : Parsec Const := do
      let i ← Parser.int
      return Const.I i
    bool : Parsec Const := do
      let b ← Parser.bool
      return Const.B b
end Const

instance instParserTermConst : Parser.Term Const :=
  ⟨Const.parse⟩
instance instToStringConst : ToString Const :=
  ⟨Const.toString⟩
instance instToSmt2Const : ToSmt2 Const :=
  ⟨Const.toSmt2⟩



inductive Op
| eq
| le | lt | ge | gt
| add | sub | mul
deriving BEq

namespace Op
  protected def toString : Op → String
    | eq => "="
    | le => "<="
    | lt => "<"
    | ge => ">="
    | gt => ">"
    | add => "+"
    | sub =>  "-"
    | mul => "*"

  def toSmt2 : Op → Writer :=
    Writer.pushStr ∘ Op.toString

  def parse : Parsec Op := do
    𝕂 Op.eq <$> pstring "="
    <|> 𝕂 Op.le <$> pstring "<="
    <|> 𝕂 Op.lt <$> pstring "<"
    <|> 𝕂 Op.ge <$> pstring ">="
    <|> 𝕂 Op.gt <$> pstring ">"
    <|> 𝕂 Op.add <$> pstring "*"
    <|> 𝕂 Op.add <$> pstring "-"
    <|> 𝕂 Op.mul <$> pstring "+"
end Op

instance instToStringOp : ToString Op :=
  ⟨Op.toString⟩



inductive Term where
| var : Symbol → Term
| cst : Const → Term
| app : Op → Array Term → Term

namespace Term
  def ident : String → Term :=
    Term.var ∘ Symbol.mk
  def nat : Nat → Term :=
    Term.cst ∘ Const.nat
  def int : Int → Term :=
    Term.cst ∘ Const.int
  def bool : Bool → Term :=
    Term.cst ∘ Const.bool

  def add (l r : Term) : Term :=
    app Op.add #[l, r]
  def mul (l r : Term) : Term :=
    app Op.mul #[l, r]

  def le (l r : Term) : Term :=
    app Op.le #[l, r]
  def lt (l r : Term) : Term :=
    app Op.lt #[l, r]
  def ge (l r : Term) : Term :=
    app Op.ge #[l, r]
  def gt (l r : Term) : Term :=
    app Op.gt #[l, r]
  def eq (l r : Term) : Term :=
    app Op.eq #[l, r]

  protected partial def toString : Term → String
    | var s => toString s
    | cst c => toString c
    | app op args => Id.run do
      let mut s := s! "({op}"
      for arg in args do
        s := s! "{s} {arg.toString}"
      s! "{s})"

  partial def toSmt2 : Term → Writer
    | var s =>
      s.toString |> Writer.pushStr
    | cst c =>
      c.toSmt2
    | app op args => do
      Writer.pushStr "("
      op.toSmt2
      for arg in args do
        Writer.pushStr " "
        arg.toSmt2
      Writer.pushStr ")"

  partial def parse : Parsec Term := do
    var <|> app <|> cst
  where
    var : Parsec Term := do
      Term.var <$> Symbol.parse
    cst : Parsec Term := do
      Term.cst <$> Const.parse
    app : Parsec Term := do
      let _ ← pchar '('
      ws
      let op ← Op.parse
      ws
      let args ← Parser.andWs Term.parse |> many1
      let _ ← pchar ')'
      match (op, args) with
      | (Op.sub, #[Term.cst (Const.I i)]) =>
        return -i |> Const.I |> Term.cst
      | _ =>
        return Term.app op args
end Term

instance instToStringTerm : ToString Term :=
  ⟨Term.toString⟩
instance instToSmt2Term : ToSmt2 Term :=
  ⟨Term.toSmt2⟩
instance instParserTermTerm : Parser.Term Term :=
  ⟨Term.parse⟩



abbrev Model :=
  Parser.Model Symbol Typ Const
abbrev Values :=
  Parser.Values Term Const


open Lsmt2.Smt in
open Lsmt2.Io in
def test : Lsmt2.ScriptU Id := do
  let n1 := Term.ident "n1"
  let n2 := Term.ident "n2"

  declareConst n1 Typ.Int
  declareConst n2 Typ.Int

  let constraint :=
    Term.le
      (Term.add n1 <| Term.nat 1)
      (Term.mul n2 <| Term.nat 2)
  assert constraint

  if ← checksat then
    let model : Model ← getModel
    model.foldlM
      (fun _ elm =>
        Io.println s! "let {elm.sym} : {elm.typ} := {elm.val}")
      ()
    let query := ["n1", "n2", "(+ n1 n2)"]
    let values : Values ← getValues query
    values.foldlM
      (fun _ (sym, val) => 
        Io.println s! "let {sym} := {val}")
      ()
  else
    Io.println "[unreachable] ain't sat"
    
#eval do
  let solver ← Lsmt2.Solver.mkZ3
  solver.runToIO test