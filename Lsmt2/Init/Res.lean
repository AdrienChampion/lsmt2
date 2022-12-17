/-! # Error-Handling -/

namespace Lsmt2



/-! ### Error Types -/

/-- The source of an error, see [`Error`]. -/
inductive Error.Src
| io : IO.Error → Error.Src
| msg : String → Error.Src

instance instToStringErrorSrc : ToString Error.Src where
  toString
  | .io e => toString e
  | .msg s => s

instance instCoeIOErrorErrorSrc
: Coe IO.Error Error.Src where
  coe := Error.Src.io

instance instCoeStringErrorSrc
: Coe String Error.Src where
  coe := Error.Src.msg



/-- A piece of error context, see [`Error`]. -/
abbrev Error.Ctx := String



/-- A error: a source and a context made of a list of context pieces. -/
structure Error where
  --- Source.
  src : Error.Src
  --- Context.
  ctx : List Error.Ctx

def Error.pretty
  (error : Error)
: String := Id.run do
  let mut s := toString error.src
  for ctx in error.ctx.reverse do
    s := ctx ++ "\n- " ++ s
  s

instance instToStringError : ToString Error where
  toString := Error.pretty

instance instCoeErrorSrcError
: Coe Error.Src Error where
  coe src := ⟨src, []⟩

instance instCoeCoeError
  (α : Type u)
  [Coe α Error.Src]
: Coe α Error where
  coe src := src



/-! ### Result Monads -/

/-- Result ([`Except`]) transformer for [`Error`]. -/
abbrev ResT (mon : Type → Type v) (α : Type) :=
  ExceptT Error mon α

instance instCoeErrorResT
  (mon : Type → Type u)
  [Mon : Monad mon]
: Coe Error <| ResT mon α where
  coe err :=
    .error err
    |> Mon.pure

instance instCoeErrorToResT
  (mon : Type → Type u)
  [Mon : Monad mon]
  (α : Type)
  [Coe α Error]
: Coe α <| ResT mon α where
  coe err :=
    .error err
    |> Mon.pure

/-- Result ([`Except`]) monad. -/
abbrev Res :=
  ResT Id

/-- A result carrying a unit value. -/
abbrev ResU :=
  Res Unit



/-! ### Context Augmentation -/

class IntoErrorCtx (α : Type u) where
  into : α → Error.Ctx

instance instIntoErrorCtxErrorCtx : IntoErrorCtx Error.Ctx where
  into := id
instance instIntoErrorCtxLazyErrorCtx : IntoErrorCtx (Unit → Error.Ctx) where
  into get := get ()

def Error.Ctx.from
  {α : Type u}
  [IntoErrorCtx α]
: α → Ctx :=
  IntoErrorCtx.into



protected def Error.Src.context'
  (src : Src)
  (ctx : χ)
  [i : IntoErrorCtx χ]
: Error where
  src := src
  ctx := [i.into ctx]

protected def Error.context'
  (err : Error)
  (ctx : χ)
  [i : IntoErrorCtx χ]
: Error :=
  { err with ctx := (i.into ctx) :: err.ctx }

protected def ResT.context
  {mon : Type → Type u}
  [Mon : Monad mon]
  (ctx : χ)
  [i : IntoErrorCtx χ]
: ResT mon α → ResT mon α :=
  Mon.map
    fun
    | .ok val => .ok val
    | .error err =>
      i.into ctx
      |> err.context'
      |> .error

protected def Res.context
  (getCtx : Unit → Error.Ctx)
: ResT Id α → ResT Id α :=
  ResT.context getCtx



/-- Extends [`Error`]s and [`Result`]s with some context. -/
class ResExt (α : Type u) (β : Type v) where
  /-- Adds context to `α`. -/
  context
    (self : α)
    (ctx : χ)
    [IntoErrorCtx χ]
  : β

export ResExt (context)

instance instResExtErrorError : ResExt Error Error where
  context err ctx :=
    Error.Ctx.from ctx |> err.context'

instance instResExtCoeError
  (α : Type u)
  [Coe α Error]
: ResExt α Error where
  context err ctx :=
    context (err : Error) ctx

instance instResExtResT
  (mon : Type → Type u)
  [Mon : Monad mon]
: ResExt (ResT mon α) (ResT mon α) where
  context res ctx :=
    res.context ctx



/-! ## Interactions with [`IO`] -/

/-- Turns itself into an IO error. -/
def Error.toIO (error : Error) : IO.Error :=
 error.pretty |> IO.Error.userError

def Res.toIO : Res α → IO α
| .ok val => pure val
| .error e => throw e.toIO

instance instMonadLiftM : MonadLift Res IO where
  monadLift := Res.toIO

def ResT.toIO (res : ResT IO α) : IO α := do
  res >>= liftM

