import Lsmt2.Init



namespace Lsmt2



/-! ## Printers -/
section Printers
  /-- Can write itself as SMT-LIB 2. -/
  class ToSmt2 (μ : Type → Type u) (α : Type) where
    /-- Writes itself, does not need to flush. -/
    write : α → μ Writer

  instance instToSmt2String : ToSmt2 IO String where
    write s := do
      Writer.pushStr s |> pure

end Printers



/-! ## Parsers

All parsers return `μ α` where `μ` is a monad, allowing for exceptions, state...
-/
section Parsers
  variable
    (μ : Type → Type u)



  class ValOfSmt2 (α : Type) where
    readVal : String → μ α

  instance instValOfSmt2String : ValOfSmt2 IO String where
    readVal s :=
      s.trim |> pure



  class TypOfSmt2 (α : Type) where
    readTyp : String → μ α

  instance instTypOfSmt2String : TypOfSmt2 IO String where
    readTyp s :=
      s.trim |> pure



  class SymOfSmt2(α : Type) where
    readSym : String → μ α

  instance instSymOfSmt2String : SymOfSmt2 IO String where
    readSym s :=
      s.trim |> pure



  class TermOfSmt2(α : Type) where
    readTerm : String → μ α

  instance instTermOfSmt2String : TermOfSmt2 IO String where
    readTerm s :=
      s.trim |> pure
end Parsers
