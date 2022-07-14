class HBind (m : Type u₁ → Type v₁) (n : Type u₂ → Type v₂) where
  hBind {α : Type u₁} {β : Type u₂} : m α → (α → n β) → n β

@[defaultInstance] instance [Bind m] : HBind m m where
  hBind := bind

instance: HBind Id.{u} Id.{v} where
  hBind {α: Type u} {β: Type v} (x: Id α) (f: α → Id β): Id β := f x
