import UnifiedBidirectionalElaboration.BinaryElaborator

abbrev Stage := Nat

mutual
  inductive Exp where
    | var    : Nat → Exp
    | «let»  : Exp → Exp → Exp
    | abs    : Exp → Exp
    | app    : Exp → Exp → Exp
    | unit   : Exp
    | quote  : Exp → Exp
    | splice : Exp → Exp
    | type   : Exp → Typ → Exp
    | stage  : Exp → Stage → Exp

  inductive Typ where
    | func : Typ → Typ → Typ
    | unit : Typ
    | code : Typ → Typ
end

structure Entry where
  type  : Typ
  stage : Stage

abbrev Ctx := Array Entry

def conv : Typ → Typ → Bool
  | .func t₁₁ t₁₂, .func t₂₁ t₂₂ => conv t₁₁ t₂₁ && conv t₂₁ t₂₂
  | .unit,         .unit         => true
  | .code t₁₁,     .code t₂₁     => conv t₁₁ t₂₁
  | _,             _             => false

-- TODO: simplify
partial def typeCheck : BinaryElaborator (Ctx × Exp) Unit Typ Stage (Except Unit)
  | (Γ, .var n₁), .check =>
    match Γ.get? n₁ with
    | none => .error ()
    | some { type := t₁, stage := s₁ } => .ok ((), t₁, s₁)

  | (Γ, .«let» e₁ e₂), mode => do
    let ((), t₁, s₁) ← typeCheck (Γ, e₁) .check
    typeCheck (Γ.push { type := t₁, stage := s₁ }, e₂) mode

  | (Γ, .abs e₁), .check₁₂ (.func a b) s =>
    typeCheck (Γ.push { type := a, stage := s }, e₁) (.check₁₂ b s)

  | (_, .abs e₁), .check₁ _ =>
    .error ()

  | (_, .abs e₁), .check₂ _ =>
    .error ()

  | (_, .abs e₁), .check =>
    .error ()

  | (Γ, .app e₁ e₂), .check₁₂ t s => do
    let ((), t₂, ()) ← typeCheck (Γ, e₂) (.check₂ s)
    typeCheck (Γ, e₁) (.check₁₂ (.func t₂ t) s)

  | (Γ, .app e₁ e₂), .check₁ t => do
    let ((), t₂, s₂) ← typeCheck (Γ, e₂) .check
    ((), (), ()) ← typeCheck (Γ, e₁) (.check₁₂ (.func t₂ t) s₂)
    .ok ((), (), s₂)

  | (Γ, .app e₁ e₂), .check₂ s => do
    if let ((), Typ.func a b, ()) ← typeCheck (Γ, e₁) (.check₂ s) then
      ((), (), ()) ← typeCheck (Γ, e₂) (.check₁₂ a s)
      .ok ((), b, ())
    else .error ()

  | (Γ, .app e₁ e₂), .check => do
    if let ((), Typ.func a b, s₁) ← typeCheck (Γ, e₁) .check then
      ((), (), ()) ← typeCheck (Γ, e₂) (.check₁₂ a s₁)
      .ok ((), b, s₁)
    else .error ()

  | (_, .unit), .check₁₂ _ _ =>
    .error ()

  | (_, .unit), .check₁ _ =>
    .error ()

  | (_, .unit), .check₂ _ =>
    .ok ((), Typ.unit, ())

  | (_, .unit), .check =>
    .error ()

  | (Γ, .quote e₁), .check₁₂ (.code t) (Nat.succ s) =>
    typeCheck (Γ, e₁) (.check₁₂ t s)

  | (Γ, .quote e₁), .check₁ (.code t) => do
    if let ((), (), Nat.succ s₁) ← typeCheck (Γ, e₁) (.check₁ t) then
      .ok ((), (), s₁)
    else .error ()

  | (Γ, .quote e₁), .check₂ (Nat.succ s) => do
    let ((), t₁, ()) ← typeCheck (Γ, e₁) (.check₂ s)
    .ok ((), Typ.code t₁, ())

  | (Γ, .quote e₁), .check => do
    if let ((), Typ.code t₁, Nat.succ s₁) ← typeCheck (Γ, e₁) .check then
      .ok ((), t₁, s₁)
    else .error ()

  | (Γ, .splice e₁), .check₁₂ t s =>
    typeCheck (Γ, e₁) (.check₁₂ (.code t) s.succ)

  | (Γ, .splice e₁), .check₁ t => do
    if let ((), (), Nat.succ s₁) ← typeCheck (Γ, e₁) (.check₁ (.code t)) then
      .ok ((), (), s₁)
    else .error ()

  | (Γ, .splice e₁), .check₂ s => do
    if let ((), Typ.code t₁, ()) ← typeCheck (Γ, e₁) (.check₂ s.succ) then
      .ok ((), t₁, ())
    else .error ()

  | (Γ, .splice e₁), .check => do
    if let ((), Typ.code t₁, Nat.succ s₁) ← typeCheck (Γ, e₁) .check then
      .ok ((), t₁, s₁)
    else .error ()

  | (Γ, .type e₁ t₁), .check => do
    let ((), (), s₁) ← typeCheck (Γ, e₁) (.check₁ t₁)
    .ok ((), t₁, s₁)

  | (Γ, .type e₁ t₁), .check₂ s => do
    ((), (), ()) ← typeCheck (Γ, e₁) (.check₁₂ t₁ s)
    .ok ((), t₁, ())

  | (Γ, .stage e₁ s₁), .check₁ t => do
    let ((), (), ()) ← typeCheck (Γ, e₁) (.check₁₂ t s₁)
    .ok ((), (), s₁)

  | (Γ, .stage e₁ s₁), .check => do
    let ((), t₁, ()) ← typeCheck (Γ, e₁) (.check₂ s₁)
    .ok ((), t₁, s₁)

  | (Γ, e), .check₁₂ ct cs => do
    let ((), st, ss) ← typeCheck (Γ, e) .check
    if conv ct st && cs == ss then .ok ((), (), ()) else .error ()

  | (Γ, e), .check₁ ct => do
    let ((), st, ss) ← typeCheck (Γ, e) .check
    if conv ct st then .ok ((), (), ss) else .error ()

  | (Γ, e), .check₂ cs => do
    let ((), st, ss) ← typeCheck (Γ, e) .check
    if cs == ss then .ok ((), st, ()) else .error ()
