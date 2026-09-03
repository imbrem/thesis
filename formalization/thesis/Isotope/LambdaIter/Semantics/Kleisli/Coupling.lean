import Isotope.LambdaIter.Models.Monadic.Coupling
import Isotope.LambdaIter.Subtyping.Semantics.Denotation

/-!
# Couplings for a set-valued `TypeModel`

`Isotope/LambdaIter/Models/Monadic/Coupling.lean` develops the coupling
(parametricity) argument that makes a monadic denotation independent of its
typing derivation, but it is phrased over a `Monadic.Model` of a `Sig`, whose
denotation is fixed at the closed free context.  The coercion-free denotation
of `Isotope/LambdaIter/Semantics/Denotation.lean` runs over a
`Subtyping.Semantics.TypeModel` and an arbitrary free context instead, so this
file redevelops the same three notions — `VRel`, `VPair`, `Coupled` — for that
interpretation.

Nothing here mentions the free context: the coupling relates two *bound*
environments over the *same* free environment, which is all the coherence
theorem needs, because no typing rule changes the free context.

The Elgot span lemma `Monadic.proj_iterate'` is genuinely model independent and
is reused rather than restated.
-/

namespace Isotope.LambdaIter.Semantics

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless

universe u v

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {m : Type v → Type v} [Monad m]

/-- Related values: equal at a common type, or the same constructor applied to
related components.  The `inl`/`inr` clauses relate values at `A ⊕ B` and
`A ⊕ B'` for unrelated `B`, `B'`, which is the slack an unannotated injection
leaves in a typing derivation. -/
inductive VRel (τ : Type u) [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    (A₁ A₂ : τ) → TyDen A₁ → TyDen A₂ → Prop where
  /-- A value is related to itself. -/
  | same {A : τ} (x : TyDen A) : VRel τ A A x x
  /-- Pairs of related components are related. -/
  | pair {A A' B B' : τ} {x : TyDen A} {x' : TyDen A'}
      {y : TyDen B} {y' : TyDen B'} :
      VRel τ A A' x x' → VRel τ B B' y y' →
      VRel τ (TypeFormers.tensor A B) (TypeFormers.tensor A' B')
        ((TypeModel.tensorEquiv A B).symm (x, y))
        ((TypeModel.tensorEquiv A' B').symm (x', y'))
  /-- Left injections of related values are related, whatever the two right
  summands are. -/
  | left {A A' B B' : τ} {x : TyDen A} {x' : TyDen A'} :
      VRel τ A A' x x' →
      VRel τ (TypeFormers.coprod A B) (TypeFormers.coprod A' B')
        ((TypeModel.coprodEquiv A B).symm (.inl x))
        ((TypeModel.coprodEquiv A' B').symm (.inl x'))
  /-- Right injections of related values are related. -/
  | right {A A' B B' : τ} {y : TyDen B} {y' : TyDen B'} :
      VRel τ B B' y y' →
      VRel τ (TypeFormers.coprod A B) (TypeFormers.coprod A' B')
        ((TypeModel.coprodEquiv A B).symm (.inr y))
        ((TypeModel.coprodEquiv A' B').symm (.inr y'))

section VRelLemmas

variable [InjectiveFormers τ]

/-- **Related values at one type are equal.**  This is what turns a coupling
into the coherence of a denotation. -/
theorem VRel.eq_of_ty : ∀ {A₁ A₂ : τ} {x : TyDen A₁} {y : TyDen A₂},
    VRel τ A₁ A₂ x y → ∀ e : A₁ = A₂, e ▸ x = y := by
  intro A₁ A₂ x y h
  induction h with
  | same x => intro _; rfl
  | @pair A A' B B' x x' y y' _ _ ih₁ ih₂ =>
      intro e
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.tensor_inj e
      have h1 : x = x' := ih₁ rfl
      have h2 : y = y' := ih₂ rfl
      change (TypeModel.tensorEquiv A B).symm (x, y) =
        (TypeModel.tensorEquiv A B).symm (x', y')
      rw [h1, h2]
  | @left A A' B B' x x' _ ih =>
      intro e
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e
      have h1 : x = x' := ih rfl
      change (TypeModel.coprodEquiv A B).symm (.inl x) =
        (TypeModel.coprodEquiv A B).symm (.inl x')
      rw [h1]
  | @right A A' B B' y y' _ ih =>
      intro e
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj e
      have h1 : y = y' := ih rfl
      change (TypeModel.coprodEquiv A B).symm (.inr y) =
        (TypeModel.coprodEquiv A B).symm (.inr y')
      rw [h1]

/-- Related values at one type are equal. -/
theorem VRel.eq_of {A : τ} {x y : TyDen A} (h : VRel τ A A x y) : x = y :=
  h.eq_of_ty rfl

/-- Inversion at a tensor, with the indices kept general so that the induction
never needs to unify two applications of a type former. -/
theorem VRel.tensor_inv_aux : ∀ {A₁ A₂ : τ} {x : TyDen A₁} {y : TyDen A₂},
    VRel τ A₁ A₂ x y →
    ∀ {A B A' B' : τ} (e₁ : A₁ = TypeFormers.tensor A B)
      (e₂ : A₂ = TypeFormers.tensor A' B'),
      VRel τ A A' (TypeModel.tensorEquiv A B (e₁ ▸ x)).1
          (TypeModel.tensorEquiv A' B' (e₂ ▸ y)).1 ∧
        VRel τ B B' (TypeModel.tensorEquiv A B (e₁ ▸ x)).2
          (TypeModel.tensorEquiv A' B' (e₂ ▸ y)).2 := by
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
theorem VRel.tensor_inv {A B A' B' : τ}
    {x : TyDen (TypeFormers.tensor A B)} {y : TyDen (TypeFormers.tensor A' B')}
    (h : VRel τ (TypeFormers.tensor A B) (TypeFormers.tensor A' B') x y) :
    VRel τ A A' (TypeModel.tensorEquiv A B x).1
        (TypeModel.tensorEquiv A' B' y).1 ∧
      VRel τ B B' (TypeModel.tensorEquiv A B x).2
        (TypeModel.tensorEquiv A' B' y).2 :=
  h.tensor_inv_aux rfl rfl

/-- Inversion at a coproduct, with the indices kept general. -/
theorem VRel.coprod_inv_aux : ∀ {A₁ A₂ : τ} {x : TyDen A₁} {y : TyDen A₂},
    VRel τ A₁ A₂ x y →
    ∀ {A B A' B' : τ} (e₁ : A₁ = TypeFormers.coprod A B)
      (e₂ : A₂ = TypeFormers.coprod A' B'),
      (∃ a a', TypeModel.coprodEquiv A B (e₁ ▸ x) = .inl a ∧
          TypeModel.coprodEquiv A' B' (e₂ ▸ y) = .inl a' ∧ VRel τ A A' a a') ∨
        (∃ b b', TypeModel.coprodEquiv A B (e₁ ▸ x) = .inr b ∧
          TypeModel.coprodEquiv A' B' (e₂ ▸ y) = .inr b' ∧ VRel τ B B' b b') := by
  intro A₁ A₂ x y h
  induction h with
  | same x =>
      intro A B A' B' e₁ e₂
      obtain ⟨rfl, rfl⟩ := InjectiveFormers.coprod_inj (e₁.symm.trans e₂)
      cases hx : TypeModel.coprodEquiv A B (e₁ ▸ x) with
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
theorem VRel.coprod_inv {A B A' B' : τ}
    {x : TyDen (TypeFormers.coprod A B)} {y : TyDen (TypeFormers.coprod A' B')}
    (h : VRel τ (TypeFormers.coprod A B) (TypeFormers.coprod A' B') x y) :
    (∃ a a', TypeModel.coprodEquiv A B x = .inl a ∧
        TypeModel.coprodEquiv A' B' y = .inl a' ∧ VRel τ A A' a a') ∨
      (∃ b b', TypeModel.coprodEquiv A B x = .inr b ∧
        TypeModel.coprodEquiv A' B' y = .inr b' ∧ VRel τ B B' b b') :=
  h.coprod_inv_aux rfl rfl

end VRelLemmas

/-- The type of related pairs of values. -/
def VPair (τ : Type u) [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
    (A₁ A₂ : τ) : Type v :=
  {p : TyDen A₁ × TyDen A₂ // VRel τ A₁ A₂ p.1 p.2}

/-- Two computations are *coupled* when both are projections of a single
computation over related pairs.  In an arbitrary monad this is the only
available notion of "these two computations produce related values". -/
def Coupled (m : Type v → Type v) [Monad m] {A₁ A₂ : τ} (u : m (TyDen A₁))
    (v : m (TyDen A₂)) : Prop :=
  ∃ w : m (VPair τ A₁ A₂),
    (u = w >>= fun p => Pure.pure p.val.1) ∧
      (v = w >>= fun p => Pure.pure p.val.2)

namespace Coupled

variable [LawfulMonad m]

/-- A computation is coupled to itself. -/
theorem refl' {A : τ} (u : m (TyDen A)) : Coupled (τ := τ) m u u := by
  refine ⟨u >>= fun x => Pure.pure ⟨(x, x), .same x⟩, ?_, ?_⟩ <;>
    rw [bind_assoc] <;> simp

/-- Related values give coupled `pure` computations. -/
theorem pure' {A₁ A₂ : τ} {x : TyDen A₁} {y : TyDen A₂}
    (h : VRel τ A₁ A₂ x y) :
    Coupled (τ := τ) m (Pure.pure x : m (TyDen A₁)) (Pure.pure y) :=
  ⟨Pure.pure ⟨(x, y), h⟩, by simp, by simp⟩

/-- **Couplings compose with `bind`.**  This is the induction step of every
case of the coherence theorem. -/
theorem bind' {A₁ A₂ B₁ B₂ : τ} {u : m (TyDen A₁)} {v : m (TyDen A₂)}
    (h : Coupled (τ := τ) m u v) {f : TyDen A₁ → m (TyDen B₁)}
    {g : TyDen A₂ → m (TyDen B₂)}
    (hfg : ∀ p : VPair τ A₁ A₂, Coupled (τ := τ) m (f p.val.1) (g p.val.2)) :
    Coupled (τ := τ) m (u >>= f) (v >>= g) := by
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
theorem eq [InjectiveFormers τ] {A : τ} {u v : m (TyDen A)}
    (h : Coupled (τ := τ) m u v) : u = v := by
  obtain ⟨w, hu, hv⟩ := h
  rw [hu, hv]
  exact bind_congr fun p => congrArg _ p.property.eq_of

end Coupled

section Iteration

open Isotope.Elgot

variable [LawfulMonad m] [Iterate m] [InjectiveFormers τ]

omit [LawfulMonad m] [Iterate m] in
/-- At a coproduct, a related pair really does come from one summand on both
sides. -/
theorem VPair.coprod_left {B₁ A₁ B₂ A₂ : τ}
    (r : VPair τ (TypeFormers.coprod B₁ A₁) (TypeFormers.coprod B₂ A₂))
    (h : ¬ ∃ q : VPair τ B₁ B₂,
      TypeModel.coprodEquiv B₁ A₁ r.val.1 = .inl q.val.1 ∧
        TypeModel.coprodEquiv B₂ A₂ r.val.2 = .inl q.val.2) :
    ∃ q : VPair τ A₁ A₂,
      TypeModel.coprodEquiv B₁ A₁ r.val.1 = .inr q.val.1 ∧
        TypeModel.coprodEquiv B₂ A₂ r.val.2 = .inr q.val.2 := by
  rcases r.property.coprod_inv with ⟨a, a', h1, h2, hr⟩ | ⟨c, c', h1, h2, hr⟩
  · exact absurd ⟨⟨(a, a'), hr⟩, h1, h2⟩ h
  · exact ⟨⟨(c, c'), hr⟩, h1, h2⟩

/-- Split a related pair at a coproduct into a related pair on the summand
that *both* sides take. -/
noncomputable def splitPair {B₁ A₁ B₂ A₂ : τ}
    (r : VPair τ (TypeFormers.coprod B₁ A₁) (TypeFormers.coprod B₂ A₂)) :
    VPair τ B₁ B₂ ⊕ VPair τ A₁ A₂ :=
  open Classical in
  if h : ∃ q : VPair τ B₁ B₂,
      TypeModel.coprodEquiv B₁ A₁ r.val.1 = .inl q.val.1 ∧
        TypeModel.coprodEquiv B₂ A₂ r.val.2 = .inl q.val.2
    then .inl h.choose
    else .inr (VPair.coprod_left r h).choose

omit [LawfulMonad m] [Iterate m] in
@[simp] theorem splitPair_fst {B₁ A₁ B₂ A₂ : τ}
    (r : VPair τ (TypeFormers.coprod B₁ A₁) (TypeFormers.coprod B₂ A₂)) :
    Sum.map (fun p : VPair τ B₁ B₂ => p.val.1)
        (fun p : VPair τ A₁ A₂ => p.val.1) (splitPair r) =
      TypeModel.coprodEquiv B₁ A₁ r.val.1 := by
  classical
  unfold splitPair
  split
  · rename_i h; exact (h.choose_spec.1).symm
  · rename_i h; exact ((VPair.coprod_left r h).choose_spec.1).symm

omit [LawfulMonad m] [Iterate m] in
@[simp] theorem splitPair_snd {B₁ A₁ B₂ A₂ : τ}
    (r : VPair τ (TypeFormers.coprod B₁ A₁) (TypeFormers.coprod B₂ A₂)) :
    Sum.map (fun p : VPair τ B₁ B₂ => p.val.2)
        (fun p : VPair τ A₁ A₂ => p.val.2) (splitPair r) =
      TypeModel.coprodEquiv B₂ A₂ r.val.2 := by
  classical
  unfold splitPair
  split
  · rename_i h; exact (h.choose_spec.2).symm
  · rename_i h; exact ((VPair.coprod_left r h).choose_spec.2).symm

/-- **Iteration preserves couplings.**  Given loop bodies coupled at every
related pair of states, the two iterations are coupled.  The proof runs the two
loops as one loop over related pairs and identifies each projection by Elgot
naturality followed by uniformity, via `Monadic.proj_iterate'`. -/
theorem Coupled.iterate [LawfulElgotMonad m] {A₁ A₂ B₁ B₂ : τ}
    {u : TyDen A₁ → m (TyDen (TypeFormers.coprod B₁ A₁))}
    {v : TyDen A₂ → m (TyDen (TypeFormers.coprod B₂ A₂))}
    (h : ∀ p : VPair τ A₁ A₂, Coupled (τ := τ) m (u p.val.1) (v p.val.2))
    (p : VPair τ A₁ A₂) :
    Coupled (τ := τ) m
      (Elgot.iter (fun x => u x >>= fun s => pure (TypeModel.coprodEquiv B₁ A₁ s))
        p.val.1)
      (Elgot.iter (fun y => v y >>= fun s => pure (TypeModel.coprodEquiv B₂ A₂ s))
        p.val.2) := by
  classical
  choose w hw₁ hw₂ using h
  refine ⟨Elgot.iter (fun q => w q >>= fun r => pure (splitPair r)) p, ?_, ?_⟩
  · refine (Monadic.proj_iterate' (fun q => w q >>= fun r => pure (splitPair r))
      (fun p : VPair τ B₁ B₂ => p.val.1) (fun p : VPair τ A₁ A₂ => p.val.1)
      (fun x => u x >>= fun s => pure (TypeModel.coprodEquiv B₁ A₁ s)) ?_ p).symm
    intro q
    simp only [bind_assoc, pure_bind, splitPair_fst, hw₁ q]
  · refine (Monadic.proj_iterate' (fun q => w q >>= fun r => pure (splitPair r))
      (fun p : VPair τ B₁ B₂ => p.val.2) (fun p : VPair τ A₁ A₂ => p.val.2)
      (fun y => v y >>= fun s => pure (TypeModel.coprodEquiv B₂ A₂ s)) ?_ p).symm
    intro q
    simp only [bind_assoc, pure_bind, splitPair_snd, hw₂ q]

end Iteration

/-- Two bound environments are related when they are related slot by slot. -/
def EnvRel (τ : Type u) [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
    {n : Nat} {β₁ β₂ : BoundCtx τ n} (ρ₁ : BoundDen β₁) (ρ₂ : BoundDen β₂) :
    Prop :=
  ∀ i : Fin n, VRel τ (β₁.get i) (β₂.get i)
    (BoundDen.get ρ₁ i) (BoundDen.get ρ₂ i)

/-- Every bound environment is related to itself. -/
theorem EnvRel.refl' {n : Nat} {β : BoundCtx τ n} (ρ : BoundDen β) :
    EnvRel τ ρ ρ := fun _ => .same _

/-- Extending related environments by related values keeps them related. -/
theorem EnvRel.snoc {n : Nat} {β₁ β₂ : BoundCtx τ n} {ρ₁ : BoundDen β₁}
    {ρ₂ : BoundDen β₂} (hρ : EnvRel τ ρ₁ ρ₂) {A₁ A₂ : τ} {x : TyDen A₁}
    {y : TyDen A₂} (hxy : VRel τ A₁ A₂ x y) :
    EnvRel τ (β₁ := β₁.snoc A₁) (β₂ := β₂.snoc A₂) (ρ₁, x) (ρ₂, y) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact hxy
  · exact hρ j

end Isotope.LambdaIter.Semantics
