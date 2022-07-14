import HBind.HBind
import HBind.ElabHdo

set_option trace.Elab.do true

-- Elaborating with `hdo` gives us a term based on `hBind`
def test_IO: IO Unit := hdo
  IO.println "Lean4"
  IO.println "hBind"
  return ()
#print test_IO

def get_0: Id Nat :=
  pure 0
def get_1: Id ((α: Type) → α → α) :=
  pure @id
def get_any: Id PUnit.{u+1} :=
  pure .unit

-- Heterogeneous bind succeeds
example: Id Unit :=
  HBind.hBind get_0 fun _ =>
  HBind.hBind get_1 fun _ =>
  pure ()

-- If we specify the monad as a polymorphic one, elaboration succeeds
-- We hacked the universe name so we have to define it
universe u in
example: Id Unit := hdo (monad := Id.{u})
  let _ ← get_0
  let _ ← get_1
  let _ ← get_any.{2}
  get_any.{0}
