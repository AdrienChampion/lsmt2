import Lean.Data.Parsec

import Lsmt2.Solver



namespace Lsmt2



export Lean (Parsec)
open Lean.Parsec



namespace Parser
  class Sym (α : Type) where
    parseSym : Parsec α
  class Typ (α : Type) where
    parseTyp : Parsec α
  class Term (α : Type) where
    parseTerm : Parsec α

  export Sym (parseSym)
  export Typ (parseTyp)
  export Term (parseTerm)

  structure Ident where
    ident : String
    quoted : Bool

  def Ident.toString : Ident → String
    | ⟨id, true⟩ => s!"|{id}|"
    | ⟨id, false⟩ => id

  instance instToStringIdent : ToString Ident where
    toString := Ident.toString

  namespace Ident
    def mkPlain (ident : String) : Ident :=
      ⟨ident, false⟩
    def mkQuoted (ident : String) : Ident :=
      ⟨ident, true⟩

    def isUnquotedHeadChar : Char → Bool
      | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'g' | 'h' | 'i' | 'j'
      | 'k' | 'l' | 'm' | 'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't'
      | 'u' | 'v' | 'w' | 'x' | 'y' | 'z'
      | '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-'
      | '+' | '=' | '<' | '>' | '.' | '?' | '/' => true
      | _ => false
    def parseUnquotedHeadChar : Parsec Char := do
      satisfy isUnquotedHeadChar

    def isUnquotedTailChar : Char → Bool
      | '0' | '1' | '2' | '3' | '4'
      | '5' | '6' | '7' | '8' | '9' => true
      | c => isUnquotedHeadChar c
    def parseUnquotedTailChar : Parsec Char := do
      satisfy isUnquotedTailChar

    def isQuotedChar : Char → Bool
      | '|' | '\\' => false
      | _ => true
    def parseQuotedChar : Parsec Char := do
      satisfy isQuotedChar



    /-- Parses idents and keywords. -/
    def parse? : Parsec <| Option Ident := do
      match ← peek? with
      | none =>
        return none
      | some '|' =>
          skip
          let id ← many1Chars parseQuotedChar
          match ← anyChar with
          | '|' => return Ident.mkQuoted id
          | c => fail s!"illegal end of quoted identifier '{c}', expected '|'"
      | some c =>
        if isUnquotedHeadChar c then
          let id ← manyChars parseUnquotedTailChar
          return Ident.mkPlain id
        else
          return none

    def parse : Parsec Ident := do
      if let some ident ← Ident.parse?
      then return ident
      else fail "expected identifier"

    #eval
      let s := "some~~ident!? something else".iter
      match parse s with
      | .success _ res => println! s!"res: '{res}'"
      | .error _ e => println! s!"err: '{e}'"
    #eval
      let s := "|some&[{!+*)=*&]&{+})(!{}#=)#*{}(   \n\n~~ident!?| something else".iter
      match parse s with
      | .success _ res => println! s!"res: '{res}'"
      | .error _ e => println! s!"err: '{e}'"

  end Ident



  def wsAnd (thn : Parsec α) : Parsec α := do
    ws
    thn



  def delimited (start : String) (p : Parsec α) (stop : String) : Parsec α := do
    let _ ← pstring start
    ws
    let res ← p
    ws
    let _ ← pstring stop
    return res



  def rawNat? : Parsec <| Option String := do
    let s ← many1Chars digit
    if s.isEmpty then
      return none
    else
      return some s

  def nat? : Parsec <| Option Nat := do
    let s? ← rawNat?
    return s? >>= String.toNat?
  
  def nat : Parsec Nat := do
    if let some n ← nat? then
      return n
    else
      fail "expected natural number"



  partial def sexpr : Parsec Bool :=
    sexprAux 0
  where sexprAux (paren : Nat) : Parsec Bool := do
    ws
    let c ← peek?
    skip
    match c with
    | '(' =>
      sexprAux (paren + 1)
    | ')' =>
      if let paren + 1 := paren then
        sexprAux paren
      else
        fail s!"ill-formed s-expression"
    | '|' =>
      let rec drain : Parsec PUnit := do
        let c ← peek?
        skip
        match c with
        | '|' => return ()
        | some _ => drain
        | none => return ()
      drain
      sexprAux paren
    | some _ =>
      sexprAux paren
    | none =>
      return paren = 0
end Parser



instance instSymIdent : Parser.Sym Parser.Ident where
  parseSym := Parser.Ident.parse

instance instTermNat : Parser.Term Nat where
  parseTerm := Parser.nat



namespace Parser
  structure ModelElm (σ τ α : Type) where
    sym : σ
    args : Array (σ × τ)
    typ : τ
    val : α

  def ModelElm.parseArgs
    [Sym σ]
    [Typ τ]
  : Parsec <| σ × τ := do
    let _ ← pchar '('
    ws
    let sym ← parseSym
    ws
    let typ ← parseTyp
    let _ ← pchar ')'
    return (sym, typ)

  def ModelElm.parse
    [Sym σ]
    [Typ τ]
    [Term α]
  : Parsec <| ModelElm σ τ α := do
    let _ ← pchar '('
    ws
    let _ ← pstring "define-fun"
    ws
    let sym ← parseSym
    ws
    let _ ← pchar '('
    let args ← wsAnd ModelElm.parseArgs |> many
    ws
    let _ ← pchar ')'
    ws
    let typ ← parseTyp
    ws
    let val ← parseTerm
    ws
    let _ ← pchar ')'
    return ⟨sym, args, typ, val⟩



  abbrev Model (σ τ α : Type) :=
    Array <| ModelElm σ τ α

  def Model.parse
    [Sym σ]
    [Typ τ]
    [Term α]
  : Parsec <| Model σ τ α := do
    let _ ← pchar '('
    ws
    let _ ← pstring "model"
    let model ← wsAnd ModelElm.parse |> many
    ws
    let _ ← pchar ')'
    return model



  def getModel
    [Sym σ]
    [Typ τ]
    [Term α]
  : Parsec <| Model σ τ α :=
    Model.parse



  def getValuesElm
    [Sym σ]
    [Term α]
  : Parsec <| σ × α := do
    let _ ← pchar '('
    ws
    let sym ← parseSym
    ws
    let val ← parseTerm
    ws
    let _ ← pchar ')'
    return (sym, val)

  abbrev Values (σ α : Type) :=
    Array <| σ × α

  def getValues
    [Sym σ]
    [Term α]
  : Parsec <| Values σ α := do
    let _ ← pchar '('
    let values ← wsAnd getValuesElm |> many
    let _ ← pchar ')'
    return values

end Parser
