inductive Mode (α : Type _) where
  | check : α → Mode α
  | synth : Mode α

def complement : {α : Type _} → Mode α → Type _
  | _, .check _ => Unit
  | α, .synth   => α

postfix:max "ᶜ" => complement

class UnaryElaborator (α β τ : Type _) (m : Type _ → Type _) [Monad m] where
  elaborate : α → (mode : Mode τ) → m (β × modeᶜ)
  sub : τ → τ → Bool
