import UnifiedBidirectionalElaboration.UnaryElaborator

mutual
  inductive Exp where
    | var   : Nat → Exp
    | «let» : Exp → Exp → Exp
    | abs   : Exp → Exp
    | app   : Exp → Exp → Exp
    | unit  : Exp
    | anno  : Exp → Typ → Exp

  inductive Typ where
    | func : Typ → Typ → Typ
    | unit : Typ
end

abbrev Ctx := Array Typ

def conv : Typ → Typ → Bool
  | .func t₁₁ t₁₂, .func t₂₁ t₂₂ => conv t₁₁ t₂₁ && conv t₂₁ t₂₂
  | .unit,         .unit         => true
  | _,             _             => false

partial def typeCheck : UnaryElaborator (Ctx × Exp) Unit Typ (Except Unit)
  -- check & synth

  | (Γ, .«let» e₁ e₂), mode => do
    let ((), t₁) ← typeCheck (Γ, e₁) .synth
    typeCheck (Γ.push t₁, e₂) mode

  -- check

  | (Γ, .abs e₁), .check (.func a b) =>
    typeCheck (Γ.push a, e₁) (.check b)

  | (Γ, .app e₁ e₂), .check t => do
    let ((), t₂) ← typeCheck (Γ, e₂) .synth
    typeCheck (Γ, e₁) (.check (.func t₂ t))

  | (Γ, e), .check expected => do
    let ((), actual) ← typeCheck (Γ, e) .synth
    if conv expected actual then .ok ((), ()) else .error ()

  -- synth

  | (Γ, .var n₁), .synth =>
    match Γ.get? n₁ with
    | none    => .error ()
    | some t₁ => .ok ((), t₁)

  | (_, .abs _), .synth => .error ()

  | (Γ, .app e₁ e₂), .synth => do
    if let ((), Typ.func a b) ← typeCheck (Γ, e₁) .synth then
      ((), ()) ← typeCheck (Γ, e₂) (.check a)
      .ok ((), b)
    else .error ()

  | (Γ, .unit), .synth =>
    .ok ((), Typ.unit)

  | (Γ, .anno e₁ t₂), .synth => do
    ((), ()) ← typeCheck (Γ, e₁) (.check t₂)
    .ok ((), t₂)
