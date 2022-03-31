inductive Mode (τ₁ τ₂ : Type _) where
  | check₁₂ : τ₁ → τ₂ → Mode τ₁ τ₂
  | check₁  : τ₁ → Mode τ₁ τ₂
  | check₂  : τ₂ → Mode τ₁ τ₂
  | check   : Mode τ₁ τ₂

def complement : {τ₁ τ₂ : Type _} → Mode τ₁ τ₂ → (Type _ × Type _)
  | _,  _,  .check₁₂ _ _ => (Unit, Unit)
  | _,  τ₂, .check₁ _    => (Unit, τ₂)
  | τ₁, _,  .check₂ _    => (τ₁, Unit)
  | τ₁, τ₂, .check       => (τ₁, τ₂)

postfix:max "ᶜ" => complement

abbrev BinaryElaborator (α β τ₁ τ₂ : Type _) (m : Type _ → Type _) [Monad m] :=
  α → (mode : Mode τ₁ τ₂) → m (β × (modeᶜ).fst × (modeᶜ).snd)
