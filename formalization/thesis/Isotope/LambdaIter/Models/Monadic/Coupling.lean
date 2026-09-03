import Isotope.LambdaIter.Models.Monadic.Model

/-!
# Couplings: how a monadic denotation becomes independent of its derivation

`Alg.coh` demands that the interpretation of a term not depend on the typing
derivation chosen for it.  For lambda-seq that is nearly free, because typing
is unique.  For lambda-case and lambda-iter it is not: `abort` types at every
result type and `inl` leaves the *other* summand unconstrained, so one term has
derivations at genuinely different types, and two derivations of one term at
one type can have sub-derivations at different types.

The naive repair fails: it is **not** true that two derivations of a term at
different types denote computations that agree after any continuation.
`.inl a` at `A ⊕ B` and at `A ⊕ B'` denote perfectly ordinary, distinct
computations.  What *is* true is that they are *coupled*: both arise from one
computation over the type of related pairs.  This file makes that precise.

* `VRel M A₁ A₂ x y` — the values `x : ⟦A₁⟧` and `y : ⟦A₂⟧` are related: equal
  when the types are, or built by the same constructor from related parts.  It
  is an inductive family over *values*, which is what makes it definable at an
  abstract type universe, where a relation defined by recursion on types is
  not.
* `VPair M A₁ A₂` — the type of related pairs.
* `Coupled M u v` — the computations `u` and `v` are the two projections of a
  single computation over `VPair`.  This is the only form of "relatedness of
  computations" available in an arbitrary monad, where a relation on values
  does not lift to one on computations.

Two facts drive everything: `Coupled` is closed under `bind` (so the
denotation of a term is coupled to itself along any derivations), and a
coupling at a *single* type is an equality (`Coupled.eq`), which is `coh`.

Injectivity and disjointness of the type formers (`InjectiveFormers`) is used
exactly twice, to invert `VRel` at a tensor and at a coproduct.
-/

namespace Isotope.LambdaIter.Monadic

universe u v

variable {S : Sig.{u}} {m : Type v → Type v} [Monad m]

/-- Related values: equal at a common type, or the same constructor applied to
related components.  The `inl`/`inr` clauses are what make the relation
non-trivial: they relate values at `A ⊕ B` and `A ⊕ B'` for unrelated `B`,
`B'`, which is exactly the slack that unannotated `inl` leaves in a typing
derivation. -/
inductive VRel (M : Model.{u, v} S m) :
    (A₁ A₂ : S.Ty) → M.interp A₁ → M.interp A₂ → Prop where
  /-- A value is related to itself. -/
  | same {A : S.Ty} (x : M.interp A) : VRel M A A x x
  /-- Pairs of related components are related. -/
  | pair {A A' B B' : S.Ty} {x : M.interp A} {x' : M.interp A'}
      {y : M.interp B} {y' : M.interp B'} :
      VRel M A A' x x' → VRel M B B' y y' →
      VRel M (tensor A B) (tensor A' B')
        ((M.tensorEquiv A B).symm (x, y)) ((M.tensorEquiv A' B').symm (x', y'))
  /-- Left injections of related values are related, whatever the two right
  summands are. -/
  | left {A A' B B' : S.Ty} {x : M.interp A} {x' : M.interp A'} :
      VRel M A A' x x' →
      VRel M (coprod A B) (coprod A' B')
        ((M.coprodEquiv A B).symm (.inl x))
        ((M.coprodEquiv A' B').symm (.inl x'))
  /-- Right injections of related values are related. -/
  | right {A A' B B' : S.Ty} {y : M.interp B} {y' : M.interp B'} :
      VRel M B B' y y' →
      VRel M (coprod A B) (coprod A' B')
        ((M.coprodEquiv A B).symm (.inr y))
        ((M.coprodEquiv A' B').symm (.inr y'))

section VRelLemmas

variable {M : Model.{u, v} S m} [InjectiveFormers S.Ty]

/-- **Related values at one type are equal.**  This is what turns a coupling
into the coherence of a denotation. -/
theorem VRel.eq_of_ty : ∀ {A₁ A₂ : S.Ty} {x : M.interp A₁} {y : M.interp A₂},
    VRel M A₁ A₂ x y → ∀ e : A₁ = A₂, e ▸ x = y := by
  intro A₁ A₂ x y h
  induction h with
  | same x => intro _; rfl
  | @pair A A' B B' x x' y y' _ _ ih₁ ih₂ =>
      intro e
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.tensor_inj e
      have h1 : x = x' := ih₁ rfl
      have h2 : y = y' := ih₂ rfl
      change (M.tensorEquiv A B).symm (x, y) = (M.tensorEquiv A B).symm (x', y')
      rw [h1, h2]
  | @left A A' B B' x x' _ ih =>
      intro e
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e
      have h1 : x = x' := ih rfl
      change (M.coprodEquiv A B).symm (.inl x) = (M.coprodEquiv A B).symm (.inl x')
      rw [h1]
  | @right A A' B B' y y' _ ih =>
      intro e
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e
      have h1 : y = y' := ih rfl
      change (M.coprodEquiv A B).symm (.inr y) = (M.coprodEquiv A B).symm (.inr y')
      rw [h1]

/-- Related values at one type are equal. -/
theorem VRel.eq_of {A : S.Ty} {x y : M.interp A} (h : VRel M A A x y) : x = y :=
  h.eq_of_ty rfl

/-- Inversion at a tensor, with the indices kept general so that the induction
never needs to unify two applications of a type former. -/
theorem VRel.tensor_inv_aux : ∀ {A₁ A₂ : S.Ty} {x : M.interp A₁}
    {y : M.interp A₂}, VRel M A₁ A₂ x y →
    ∀ {A B A' B' : S.Ty} (e₁ : A₁ = tensor A B) (e₂ : A₂ = tensor A' B'),
      VRel M A A' (M.tensorEquiv A B (e₁ ▸ x)).1
          (M.tensorEquiv A' B' (e₂ ▸ y)).1 ∧
        VRel M B B' (M.tensorEquiv A B (e₁ ▸ x)).2
          (M.tensorEquiv A' B' (e₂ ▸ y)).2 := by
  intro A₁ A₂ x y h
  induction h with
  | same x =>
      intro A B A' B' e₁ e₂
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.tensor_inj (e₁.symm.trans e₂)
      exact ⟨.same _, .same _⟩
  | @pair A₀ A₀' B₀ B₀' x x' y y' h₁ h₂ _ _ =>
      intro A B A' B' e₁ e₂
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.tensor_inj e₁
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.tensor_inj e₂
      simpa using ⟨h₁, h₂⟩
  | left _ _ =>
      intro _ _ _ _ e₁ _
      exact absurd e₁.symm InjectiveFormers.tensor_ne_coprod
  | right _ _ =>
      intro _ _ _ _ e₁ _
      exact absurd e₁.symm InjectiveFormers.tensor_ne_coprod

/-- Inversion at a tensor: related pairs have related components. -/
theorem VRel.tensor_inv {A B A' B' : S.Ty} {x : M.interp (tensor A B)}
    {y : M.interp (tensor A' B')}
    (h : VRel M (tensor A B) (tensor A' B') x y) :
    VRel M A A' (M.tensorEquiv A B x).1 (M.tensorEquiv A' B' y).1 ∧
      VRel M B B' (M.tensorEquiv A B x).2 (M.tensorEquiv A' B' y).2 :=
  h.tensor_inv_aux rfl rfl

/-- Inversion at a coproduct, with the indices kept general. -/
theorem VRel.coprod_inv_aux : ∀ {A₁ A₂ : S.Ty} {x : M.interp A₁}
    {y : M.interp A₂}, VRel M A₁ A₂ x y →
    ∀ {A B A' B' : S.Ty} (e₁ : A₁ = coprod A B) (e₂ : A₂ = coprod A' B'),
      (∃ a a', M.coprodEquiv A B (e₁ ▸ x) = .inl a ∧
          M.coprodEquiv A' B' (e₂ ▸ y) = .inl a' ∧ VRel M A A' a a') ∨
        (∃ b b', M.coprodEquiv A B (e₁ ▸ x) = .inr b ∧
          M.coprodEquiv A' B' (e₂ ▸ y) = .inr b' ∧ VRel M B B' b b') := by
  intro A₁ A₂ x y h
  induction h with
  | same x =>
      intro A B A' B' e₁ e₂
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj (e₁.symm.trans e₂)
      cases hx : M.coprodEquiv A B (e₁ ▸ x) with
      | inl a => exact Or.inl ⟨a, a, rfl, rfl, .same _⟩
      | inr b => exact Or.inr ⟨b, b, rfl, rfl, .same _⟩
  | pair _ _ _ _ =>
      intro _ _ _ _ e₁ _
      exact absurd e₁ InjectiveFormers.tensor_ne_coprod
  | @left A₀ A₀' B₀ B₀' x x' h _ =>
      intro A B A' B' e₁ e₂
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e₁
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e₂
      exact Or.inl ⟨_, _, by simp, by simp, h⟩
  | @right A₀ A₀' B₀ B₀' y y' h _ =>
      intro A B A' B' e₁ e₂
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e₁
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e₂
      exact Or.inr ⟨_, _, by simp, by simp, h⟩

/-- Inversion at a coproduct: related sums take the same branch, with related
payloads. -/
theorem VRel.coprod_inv {A B A' B' : S.Ty} {x : M.interp (coprod A B)}
    {y : M.interp (coprod A' B')}
    (h : VRel M (coprod A B) (coprod A' B') x y) :
    (∃ a a', M.coprodEquiv A B x = .inl a ∧ M.coprodEquiv A' B' y = .inl a' ∧
        VRel M A A' a a') ∨
      (∃ b b', M.coprodEquiv A B x = .inr b ∧ M.coprodEquiv A' B' y = .inr b' ∧
        VRel M B B' b b') :=
  h.coprod_inv_aux rfl rfl

end VRelLemmas

/-- The type of related pairs of values. -/
def VPair (M : Model.{u, v} S m) (A₁ A₂ : S.Ty) : Type v :=
  {p : M.interp A₁ × M.interp A₂ // VRel M A₁ A₂ p.1 p.2}

/-- Two computations are *coupled* when both are projections of a single
computation over related pairs.  In an arbitrary monad this is the only
available notion of "these two computations produce related values". -/
def Coupled (M : Model.{u, v} S m) {A₁ A₂ : S.Ty} (u : m (M.interp A₁))
    (v : m (M.interp A₂)) : Prop :=
  ∃ w : m (VPair M A₁ A₂),
    (u = w >>= fun p => Pure.pure p.val.1) ∧
      (v = w >>= fun p => Pure.pure p.val.2)

namespace Coupled

variable {M : Model.{u, v} S m} [LawfulMonad m]

/-- A computation is coupled to itself. -/
theorem refl' {A : S.Ty} (u : m (M.interp A)) : Coupled M u u := by
  refine ⟨u >>= fun x => Pure.pure ⟨(x, x), .same x⟩, ?_, ?_⟩ <;>
    rw [bind_assoc] <;> simp

/-- Related values give coupled `pure` computations. -/
theorem pure' {A₁ A₂ : S.Ty} {x : M.interp A₁} {y : M.interp A₂}
    (h : VRel M A₁ A₂ x y) :
    Coupled M (Pure.pure x : m (M.interp A₁)) (Pure.pure y) :=
  ⟨Pure.pure ⟨(x, y), h⟩, by simp, by simp⟩

/-- **Couplings compose with `bind`.**  This is the induction step of every
case of the coherence theorem. -/
theorem bind' {A₁ A₂ B₁ B₂ : S.Ty} {u : m (M.interp A₁)} {v : m (M.interp A₂)}
    (h : Coupled M u v) {f : M.interp A₁ → m (M.interp B₁)}
    {g : M.interp A₂ → m (M.interp B₂)}
    (hfg : ∀ p : VPair M A₁ A₂, Coupled M (f p.val.1) (g p.val.2)) :
    Coupled M (u >>= f) (v >>= g) := by
  classical
  obtain ⟨w₀, hu, hv⟩ := h
  choose w hw₁ hw₂ using hfg
  refine ⟨w₀ >>= w, ?_, ?_⟩
  · rw [hu, bind_assoc, bind_assoc]
    exact bind_congr fun p => by rw [pure_bind, hw₁ p]
  · rw [hv, bind_assoc, bind_assoc]
    exact bind_congr fun p => by rw [pure_bind, hw₂ p]

omit [LawfulMonad m] in
/-- A coupling at a single type is an equality. -/
theorem eq [InjectiveFormers S.Ty] {A : S.Ty} {u v : m (M.interp A)}
    (h : Coupled M u v) : u = v := by
  obtain ⟨w, hu, hv⟩ := h
  rw [hu, hv]
  exact bind_congr fun p => congrArg _ p.property.eq_of

end Coupled

namespace SeqModel

variable {M : Model.{u, v} S m}

open LocallyNameless

/-- Two environments are related when they are related slot by slot. -/
def EnvRel (M : Model.{u, v} S m) {n : Nat} {β₁ β₂ : BoundCtx S.Ty n}
    (ρ₁ : M.Env β₁) (ρ₂ : M.Env β₂) : Prop :=
  ∀ i : Fin n, VRel M (β₁.get i) (β₂.get i) (Env.get ρ₁ i) (Env.get ρ₂ i)

/-- Every environment is related to itself. -/
theorem EnvRel.refl' {n : Nat} {β : BoundCtx S.Ty n} (ρ : M.Env β) :
    EnvRel M ρ ρ := fun _ => .same _

/-- Extending related environments by related values keeps them related. -/
theorem EnvRel.snoc {n : Nat} {β₁ β₂ : BoundCtx S.Ty n} {ρ₁ : M.Env β₁}
    {ρ₂ : M.Env β₂} (hρ : EnvRel M ρ₁ ρ₂) {A₁ A₂ : S.Ty} {x : M.interp A₁}
    {y : M.interp A₂} (hxy : VRel M A₁ A₂ x y) :
    EnvRel M (β₁ := β₁.snoc A₁) (β₂ := β₂.snoc A₂) (ρ₁, x) (ρ₂, y) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hxy
  · exact hρ j

end SeqModel

end Isotope.LambdaIter.Monadic
