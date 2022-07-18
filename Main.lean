import HBind.HBind
import HBind.ElabHdo
open HBind(hBind)

set_option trace.Elab.do true
set_option pp.universes true
set_option trace.Meta.synthInstance false

def main: IO Unit :=
  pure ()

--== Test utilities =========================================================--

def Dm1: Prop :=
  True
deriving Inhabited

def D0: Type 0 :=
  Nat
deriving Inhabited

def D1: Type 1 :=
  (α: Type) → α → Nat
deriving Inhabited

def Dx: Type u :=
  PUnit
deriving Inhabited

def getD0 [Monad m]: m D0 :=
  pure default

def getD1 [Monad m]: m D1 :=
  pure default

def getDx [Monad m]: m Dx :=
  pure default

--== Tests with `Id` ========================================================--

example: Id Unit :=
  hBind getD0 (fun _ => pure default)

-- The two monads in `hBind` are morally the same, but Lean won't guess that.
-- We need to indicate it by specifying the `m` parameter for the left action.
example: Id Unit :=
  hBind getD0 (m := Id) fun _ =>
  hBind getD1 (m := Id) fun _ =>
  hBind getDx.{5} (m := Id) fun _ =>
  pure default

-- The `hdo` notation automatically sets `(m := Id)` and `(n := Id)`, where
-- `Id` is an identifier with level parameters, inferred from the block's
-- expected type with universes generalized.
example: Id Unit := hdo
  let _ ← getD0
  let _ ← getD1
  let _ ← getDx.{2}
  getDx.{0}

-- Elaborating with `hdo` gives us a term based on `hBind`
def test_IO: IO Unit := hdo
  IO.println "Lean4"
  IO.println "hBind"
  return ()
#print test_IO

--== Tests with a custom monad ==============================================--

-- We have to decouple the universes of the parameter `E: Type u → Type v` from
-- those of `R: Type w` since the latter is going to vary, but not the former
inductive ITree (E: Type u → Type v) (R: Type w): Type _ :=
  | Ret (r: R)
  | Vis {T: Type _} (e: E T) (k: T → ITree E R)

namespace ITree
def ITree.pure (r: R): ITree E R :=
  Ret r
def ITree.bind (t: ITree E T) (k: T → ITree E R) :=
  match t with
  | Ret r => k r
  | Vis e kt => Vis e (fun x => bind (kt x) k)

instance: Monad (ITree E) where
  pure := ITree.pure
  bind := ITree.bind

instance: HBind (ITree E) (ITree E) where
  hBind {R₁: Type _} {R₂: Type _} (t: ITree E R₁) (k: R₁ → ITree E R₂):
    ITree E R₂ := ITree.bind t k

inductive PVoid: Type u → Type v :=

inductive E00 {α: Type _} {β: Type}: Type → Type :=
  | getNat: (n: Nat) → E00 Nat

inductive E01: Type → Type 1 :=
  | call: {α β: Type} → (f: α → β) → (x: α) → E01 β

inductive E11: Type 1 → Type 1 :=
  | mkConst: {R: Type} → (x: R) → E11 (ITree PVoid.{0,0} R)
  | trigger: {E: Type → Type} → {T: Type} → (e: E T) → E11 (ITree E T)

inductive Euv: Type u → Type _ :=
  | run: {E: Type u → Type v} → {R: Type u} → (t: ITree E R) → Euv R

example: ITree PVoid Nat :=
  HBind.hBind (m := ITree PVoid) getD0 fun _ =>
  HBind.hBind (m := ITree PVoid) getD1 fun _ =>
  pure 0

example: ITree PVoid Nat := hdo
  let _ ← getD0
  let _ ← getDx.{4}
  let _ ← getD1
  pure 0

example: ITree PVoid (ITree PVoid Nat) := hdo
  pure (.Ret 0)
