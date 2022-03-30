import UnifiedBidirectionalElaboration.UnaryElaborator

mutual
  inductive Exp where
    | var  : Nat → Exp
    | abs  : Exp → Exp
    | app  : Exp → Exp → Exp
    | anno : Exp → Typ → Exp

  inductive Typ where
    | func : Typ → Typ → Typ
    | type : Typ
end

abbrev Ctx := Array Typ

partial instance TypeValidator : UnaryElaborator (Ctx × Exp) Unit Typ (Except Unit) where
  elaborate :=
    let rec validate
      | (Γ, .abs e₁),     .check (.func a b) => validate (Γ.push a, e₁) (.check b)
      | (Γ, .app e₁ e₂),  .check t           => do
        let ((), t₂) ← validate (Γ, e₂) .synth
        validate (Γ, e₁) (.check (.func t₂ t))
      | (Γ, e),           .check t           => do
        ((), _) ← validate (Γ, e) .synth
        .ok ((), ())
      | (Γ, .var n₁),     .synth             =>
        match Γ.get? n₁ with
        | none    => .error ()
        | some t₁ => .ok ((), t₁)
      | (_, .abs _),      .synth             => .error ()
      | (Γ, .app e₁ e₂),  .synth             => do
        if let ((), Typ.func a b) ← validate (Γ, e₁) .synth then
          ((), ()) ← validate (Γ, e₂) (.check a)
          .ok ((), b)
        else .error ()
      | (Γ, .anno e₁ t₂), .synth             => do
        ((), ()) ← validate (Γ, e₁) (.check t₂)
        .ok ((), t₂)
    validate

  sub :=
    let rec conv
      | .func t₁₁ t₁₂, .func t₂₁ t₂₂ => conv t₁₁ t₂₁ && conv t₂₁ t₂₂
      | .type,         .type         => true
      | _,             _             => false
    conv
