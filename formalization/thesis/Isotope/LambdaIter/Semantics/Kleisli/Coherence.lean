import Isotope.LambdaIter.Semantics.Kleisli.Coupling
import Isotope.LambdaIter.Semantics.Kleisli.Generic

/-!
# Coherence of the coercion-free denotation in its typing derivation

Lambda-iter typing is not unique: `abort` types at every result type and `inl`
leaves the right summand free, so one term at one type admits derivations whose
sub-derivations sit at genuinely different types.  This file proves that the
set-valued denotation does not notice, by the coupling argument of
`Kleisli/Coupling.lean`, run over an *arbitrary* free context.

Two things make the free context free of charge: no typing rule changes it, and
the free-variable rule's lookup witness is a proposition, so two derivations of
`.fv x` in one context are literally the same derivation once their result
types have been identified.
-/

namespace Isotope.LambdaIter.Semantics

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.Elgot

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m] [Iterate m]
variable [InstructionModel Φ τ ε m]

/-- The generic denotation of an embedded exact derivation. -/
abbrev exactDenote {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    CtxDen Γ → BoundDen β → m (TyDen A) :=
  Subtyping.Semantics.denote (ε := ε) (m := m) h.toGeneric


section Equations

variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} (γ : CtxDen Γ)

/-- The free-variable clause. -/
@[simp] theorem exactDenote_fv {x : ν} {A : τ} (hx : Γ.lookup x = some A)
    (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.fv (Φ := Φ) (β := β) hx) γ ρ =
      pure (CtxDen.lookup γ x hx) := by
  simp only [exactDenote, HasType.toGeneric_fv, Subtyping.Semantics.denote]

/-- The bound-variable clause. -/
@[simp] theorem exactDenote_bv {i : Fin n} (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m)
        (HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := i)) γ ρ =
      pure (BoundDen.get ρ i) := by
  simp only [exactDenote, HasType.toGeneric_bv, Subtyping.Semantics.denote]

/-- The instruction clause. -/
@[simp] theorem exactDenote_op {a : Tm ν Φ n} {f : Φ}
    (ha : HasType Φ Γ β a (instrSrc f)) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.op ha) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ >>=
        InstructionModel.denote (Φ := Φ) (τ := τ) (ε := ε) (m := m) f := by
  simp only [exactDenote, HasType.toGeneric_op, Subtyping.Semantics.denote]

/-- The `let` clause. -/
@[simp] theorem exactDenote_let₁ {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B)
    (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.let₁ ha hb) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ >>= fun x =>
        exactDenote (ε := ε) (m := m) hb γ (ρ, x) := by
  simp only [exactDenote, HasType.toGeneric_let₁, Subtyping.Semantics.denote]

/-- The unit clause. -/
@[simp] theorem exactDenote_unit (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m)
        (HasType.unit (Φ := Φ) (Γ := Γ) (β := β)) γ ρ =
      pure (TypeModel.unitEquiv.symm ()) := by
  simp only [exactDenote, HasType.toGeneric_unit, Subtyping.Semantics.denote]
  rfl

/-- The pairing clause. -/
@[simp] theorem exactDenote_pair {a b : Tm ν Φ n} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.pair ha hb) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ >>= fun x =>
        exactDenote (ε := ε) (m := m) hb γ ρ >>= fun y =>
          pure ((TypeModel.tensorEquiv A B).symm (x, y)) := by
  simp only [exactDenote, HasType.toGeneric_pair, Subtyping.Semantics.denote]
  rfl

/-- The pair-elimination clause. -/
@[simp] theorem exactDenote_let₂ {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)}
    {A B C : τ} (ha : HasType Φ Γ β a (TypeFormers.tensor A B))
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.let₂ ha hc) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ >>= fun p =>
        exactDenote (ε := ε) (m := m) hc γ
          ((ρ, (TypeModel.tensorEquiv A B p).1),
            (TypeModel.tensorEquiv A B p).2) := by
  simp only [exactDenote, HasType.toGeneric_let₂, Subtyping.Semantics.denote]
  rfl

/-- The left-injection clause. -/
@[simp] theorem exactDenote_inl {a : Tm ν Φ n} {A B : τ}
    (ha : HasType Φ Γ β a A) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.inl (B := B) ha) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ >>= fun x =>
        pure ((TypeModel.coprodEquiv A B).symm (.inl x)) := by
  simp only [exactDenote, HasType.toGeneric_inl, Subtyping.Semantics.denote]
  rfl

/-- The right-injection clause. -/
@[simp] theorem exactDenote_inr {b : Tm ν Φ n} {A B : τ}
    (hb : HasType Φ Γ β b B) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.inr (A := A) hb) γ ρ =
      exactDenote (ε := ε) (m := m) hb γ ρ >>= fun y =>
        pure ((TypeModel.coprodEquiv A B).symm (.inr y)) := by
  simp only [exactDenote, HasType.toGeneric_inr, Subtyping.Semantics.denote]
  rfl

/-- The case clause. -/
@[simp] theorem exactDenote_case {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)}
    {A B C : τ} (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (hl : HasType Φ Γ (.snoc β A) l C) (hr : HasType Φ Γ (.snoc β B) r C)
    (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.case he hl hr) γ ρ =
      exactDenote (ε := ε) (m := m) he γ ρ >>= fun s =>
        match TypeModel.coprodEquiv A B s with
        | .inl x => exactDenote (ε := ε) (m := m) hl γ (ρ, x)
        | .inr y => exactDenote (ε := ε) (m := m) hr γ (ρ, y) := by
  simp only [exactDenote, HasType.toGeneric_case, Subtyping.Semantics.denote]
  rfl

/-- The `abort` clause. -/
@[simp] theorem exactDenote_abort {a : Tm ν Φ n} {C : τ}
    (ha : HasType Φ Γ β a (TypeFormers.empty : τ)) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.abort (C := C) ha) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ >>= fun z =>
        Empty.elim (TypeModel.emptyEquiv z) := by
  simp only [exactDenote, HasType.toGeneric_abort, Subtyping.Semantics.denote]
  rfl

/-- The iteration clause. -/
@[simp] theorem exactDenote_iter {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A))
    (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) (HasType.iter ha hb) γ ρ =
      exactDenote (ε := ε) (m := m) ha γ ρ >>= Elgot.iter (fun x =>
        exactDenote (ε := ε) (m := m) hb γ (ρ, x) >>= fun s =>
          pure (TypeModel.coprodEquiv B A s)) := by
  simp only [exactDenote, HasType.toGeneric_iter, Subtyping.Semantics.denote]
  rfl

end Equations

variable [LawfulElgotMonad m] [InjectiveFormers τ]

/-- **The coupling theorem.**  Any two derivations of one term, in two bound
contexts over one free context, interpreted at related bound environments and
one free environment, denote coupled computations. -/
theorem denote_coupled {Γ : Ctx ν τ} {n : Nat} {β₁ : BoundCtx τ n}
    {t : Tm ν Φ n} {A₁ : τ} (h : HasType Φ Γ β₁ t A₁) :
    ∀ {β₂ : BoundCtx τ n} {A₂ : τ} (k : HasType Φ Γ β₂ t A₂)
      (γ : CtxDen Γ) (ρ₁ : BoundDen β₁) (ρ₂ : BoundDen β₂),
      EnvRel τ ρ₁ ρ₂ →
      Coupled (τ := τ) m (exactDenote (ε := ε) h γ ρ₁)
        (exactDenote (ε := ε) k γ ρ₂) := by
  induction h with
  | @fv _ _ _ _ hx =>
      intro β₂ A₂ k γ ρ₁ ρ₂ _
      cases k with
      | fv hx' =>
          have hAA : _ = A₂ := Option.some.inj (hx.symm.trans hx')
          subst hAA
          simp only [exactDenote_fv]
          exact Coupled.pure' (τ := τ) (.same _)
  | bv =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k
      simp only [exactDenote_bv]
      exact Coupled.pure' (τ := τ) (hρ _)
  | op _ ih =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k with
      | op k' =>
          simp only [exactDenote_op]
          refine (ih k' γ ρ₁ ρ₂ hρ).bind' fun p => ?_
          rw [p.property.eq_of]
          exact Coupled.refl' (τ := τ) _
  | let₁ _ _ iha ihb =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k with
      | let₁ ka kb =>
          simp only [exactDenote_let₁]
          exact (iha ka γ ρ₁ ρ₂ hρ).bind' fun p =>
            ihb kb γ (ρ₁, p.val.1) (ρ₂, p.val.2) (hρ.snoc p.property)
  | unit =>
      intro β₂ A₂ k γ ρ₁ ρ₂ _
      cases k
      simp only [exactDenote_unit]
      exact Coupled.pure' (τ := τ) (.same _)
  | pair _ _ iha ihb =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k with
      | pair ka kb =>
          simp only [exactDenote_pair]
          exact (iha ka γ ρ₁ ρ₂ hρ).bind' fun p =>
            (ihb kb γ ρ₁ ρ₂ hρ).bind' fun q =>
              Coupled.pure' (τ := τ) (.pair p.property q.property)
  | let₂ _ _ iha ihc =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k with
      | let₂ ka kc =>
          simp only [exactDenote_let₂]
          refine (iha ka γ ρ₁ ρ₂ hρ).bind' fun p => ?_
          obtain ⟨h1, h2⟩ := p.property.tensor_inv
          exact ihc kc γ _ _ ((hρ.snoc h1).snoc h2)
  | inl _ ih =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k with
      | inl k' =>
          simp only [exactDenote_inl]
          exact (ih k' γ ρ₁ ρ₂ hρ).bind' fun p =>
            Coupled.pure' (τ := τ) (.left p.property)
  | inr _ ih =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k with
      | inr k' =>
          simp only [exactDenote_inr]
          exact (ih k' γ ρ₁ ρ₂ hρ).bind' fun p =>
            Coupled.pure' (τ := τ) (.right p.property)
  | case _ _ _ ihe ihl ihr =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k with
      | case ke kl kr =>
          simp only [exactDenote_case]
          refine (ihe ke γ ρ₁ ρ₂ hρ).bind' fun p => ?_
          rcases p.property.coprod_inv with ⟨a, a', ha, ha', hab⟩ |
            ⟨b, b', hb, hb', hab⟩
          · simp only [ha, ha']
            exact ihl kl γ (ρ₁, a) (ρ₂, a') (hρ.snoc hab)
          · simp only [hb, hb']
            exact ihr kr γ (ρ₁, b) (ρ₂, b') (hρ.snoc hab)
  | abort _ ih =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k with
      | abort k' =>
          simp only [exactDenote_abort]
          exact (ih k' γ ρ₁ ρ₂ hρ).bind' fun p =>
            (TypeModel.emptyEquiv p.val.1).elim
  | iter ha hb iha ihb =>
      intro β₂ A₂ k γ ρ₁ ρ₂ hρ
      cases k with
      | iter ka kb =>
          simp only [exactDenote_iter]
          refine (iha ka γ ρ₁ ρ₂ hρ).bind' fun p => ?_
          exact Coupled.iterate
            (u := fun x => exactDenote (ε := ε) hb γ (ρ₁, x))
            (v := fun y => exactDenote (ε := ε) kb γ (ρ₂, y))
            (fun q => ihb kb γ (ρ₁, q.val.1) (ρ₂, q.val.2) (hρ.snoc q.property))
            p

/-- **Coherence**: the coercion-free denotation does not depend on the typing
derivation chosen for a term. -/
theorem exactDenote_coh {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h k : HasType Φ Γ β t A)
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    exactDenote (ε := ε) (m := m) h γ ρ = exactDenote (ε := ε) k γ ρ :=
  (denote_coupled (ε := ε) h k γ ρ ρ (EnvRel.refl' ρ)).eq

end Isotope.LambdaIter.Semantics
