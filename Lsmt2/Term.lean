import Lsmt2.Init



namespace Lsmt2



/-! ## Printers -/
section Printers

  /-- Can write itself as SMT-LIB 2. -/
  class ToSmt2 (α : Type) where
    /-- Writes itself, does not need to flush. -/
    write : α → Writer

  instance instToSmt2String : ToSmt2 String where
    write s := do
      Writer.pushStr s

end Printers



/-! ## Parsers

All parsers return `μ α` where `μ` is a monad, allowing for exceptions, state...
-/
section Parsers

  variable
    (μ : Type → Type u)


  class ValOfSmt2 (α : Type) where
    readVal : String → μ α

  instance instValOfSmt2 : ValOfSmt2 Id String where
    readVal s := s.trim



  class TypOfSmt2 (α : Type) where
    readTyp : String → μ α

  instance instTypOfSmt2 : TypOfSmt2 Id String where
    readTyp s :=
      s.trim



  class SymOfSmt2(α : Type) where
    readSym : String → μ α

  instance instSymOfSmt2 : SymOfSmt2 Id String where
    readSym s :=
      s.trim



  class TermOfSmt2(α : Type) where
    readTerm : String → μ α

  instance instTermOfSmt2 : TermOfSmt2 Id String where
    readTerm s :=
      s.trim

end Parsers
