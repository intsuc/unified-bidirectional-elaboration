inductive Mode (τ : Type _) where
  | check : τ → Mode τ
  | synth : Mode τ

def complement : {τ : Type _} → Mode τ → Type _
  | _, .check _ => Unit
  | τ, .synth   => τ

postfix:max "ᶜ" => complement

abbrev UnaryElaborator (α β τ : Type _) (m : Type _ → Type _) [Monad m] := α → (mode : Mode τ) → m (β × modeᶜ)
