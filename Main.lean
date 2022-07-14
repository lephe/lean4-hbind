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
