import Isotope.LambdaSSA.Translation.FromSSA
import Isotope.LambdaSSA.Semantics.Monadic.Term
import Isotope.LambdaIter.Subtyping.Semantics.Denotation

/-! # Direct semantics of the SSA/exact-expression bridge -/

namespace Isotope.LambdaSSA.Translation.Expression.Semantics

set_option autoImplicit true
set_option relaxedAutoImplicit true

open Isotope.LambdaIter
open Isotope.LambdaIter.Subtyping.Semantics

universe u v q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {m : Type v → Type v} [Monad m] [LawfulMonad m]
variable [Isotope.Elgot.Iterate m] [InstructionModel Φ τ ε m]

@[simp] def envToBound : {Γ : LambdaSSA.VCtx τ} →
    LambdaSSA.Semantics.Monadic.Env Γ → BoundDen (FromSSA.boundContext Γ)
  | [], _ => PUnit.unit
  | _ :: _, ρ => (envToBound ρ.1, ρ.2)

private theorem envToBound_get {Γ : LambdaSSA.VCtx τ} {A : τ}
    (ρ : LambdaSSA.Semantics.Monadic.Env Γ) (i : Fin Γ.length)
    (h : LambdaSSA.At Γ i A) :
    HEq (BoundDen.get (envToBound ρ) i)
      (LambdaSSA.Semantics.Monadic.Env.get ρ i h) := by
  induction Γ generalizing A with
  | nil => exact Fin.elim0 i
  | cons B Γ ih =>
      revert h
      refine Fin.cases (fun h => ?_) (fun j h => ?_) i
      · simp [LambdaSSA.At] at h
        subst A
        rfl
      · exact ih ρ.1 j h

/-- Evidence that a generic derivation is exactly the constructor-preserving
embedding of an exact derivation.  In particular this relation has no `sub`
constructor. -/
inductive ExactGeneric {ν : Type*} [DecidableEq ν] : {n : Nat} →
    {Γ : Ctx ν τ} → {β : LambdaIter.LocallyNameless.BoundCtx τ n} →
    {t : LambdaIter.LocallyNameless.Tm ν Φ n} → {A : τ} →
    LambdaIter.LocallyNameless.HasType Φ Γ β t A →
    LambdaIter.Subtyping.LocallyNameless.HasType Φ Γ β t A → Prop where
  | fv : ExactGeneric (.fv h) (.fv h)
  | bv : ExactGeneric .bv .bv
  | op : ExactGeneric ha ga → ExactGeneric (.op ha) (.op ga)
  | let₁ : ExactGeneric ha ga → ExactGeneric hb gb →
      ExactGeneric (.let₁ ha hb) (.let₁ ga gb)
  | unit : ExactGeneric .unit .unit
  | pair : ExactGeneric ha ga → ExactGeneric hb gb →
      ExactGeneric (.pair ha hb) (.pair ga gb)
  | let₂ : ExactGeneric ha ga → ExactGeneric hb gb →
      ExactGeneric (.let₂ ha hb) (.let₂ ga gb)
  | inl : ExactGeneric ha ga → ExactGeneric (.inl ha) (.inl ga)
  | inr : ExactGeneric hb gb → ExactGeneric (.inr hb) (.inr gb)
  | case : ExactGeneric he ge → ExactGeneric hl gl → ExactGeneric hr gr →
      ExactGeneric (.case he hl hr) (.case ge gl gr)
  | abort : ExactGeneric ha ga → ExactGeneric (.abort ha) (.abort ga)
  | iter : ExactGeneric ha ga → ExactGeneric hb gb →
      ExactGeneric (.iter ha hb) (.iter ga gb)

/-- Constructor alignment between an SSA denotation witness and exact and
generic lambda-iter derivations over an independent raw lambda-iter term. -/
inductive Aligned : {Γ : LambdaSSA.VCtx τ} → {t : LambdaSSA.Tm Φ} → {A : τ} →
    {ht : LambdaSSA.Tm.HasType Γ t A} →
    {f : LambdaSSA.Semantics.Monadic.Env Γ → m (TyDen A)} →
    {it : LambdaIter.LocallyNameless.Tm Empty Φ Γ.length} →
    LambdaSSA.Semantics.Monadic.Denotes ε ht f →
    LambdaIter.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ)
      (FromSSA.boundContext Γ) it A →
    LambdaIter.Subtyping.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ)
      (FromSSA.boundContext Γ) it A → Prop where
  | var (i : Fin Γ.length) (h : LambdaSSA.At Γ i A)
      (e : (FromSSA.boundContext Γ).get i = A) :
      Aligned (.var h)
        (e ▸ (LambdaIter.LocallyNameless.HasType.bv (Φ := Φ)
          (Γ := (Ctx.nil : Ctx Empty τ)) (β := FromSSA.boundContext Γ) (ι := i)))
        (e ▸ (LambdaIter.Subtyping.LocallyNameless.HasType.bv (Φ := Φ)
          (Γ := (Ctx.nil : Ctx Empty τ)) (β := FromSSA.boundContext Γ) (ι := i)))
  | op (da : LambdaSSA.Semantics.Monadic.Denotes ε hta fa)
      (a : Aligned da ha ga) : Aligned (.op da) (.op ha) (.op ga)
  | let₁ (da : LambdaSSA.Semantics.Monadic.Denotes ε hta fa)
      (db : LambdaSSA.Semantics.Monadic.Denotes ε htb fb)
      (aa : Aligned da ha ga) (ab : Aligned db hb gb) :
      Aligned (.let₁ da db) (.let₁ ha hb) (.let₁ ga gb)
  | pair (da : LambdaSSA.Semantics.Monadic.Denotes ε hta fa)
      (db : LambdaSSA.Semantics.Monadic.Denotes ε htb fb)
      (aa : Aligned da ha ga) (ab : Aligned db hb gb) :
      Aligned (.pair da db) (.pair ha hb) (.pair ga gb)
  | unit : Aligned (.unit (Γ := Γ)) (.unit) (.unit)
  | let₂ (da : LambdaSSA.Semantics.Monadic.Denotes ε hta fa)
      (db : LambdaSSA.Semantics.Monadic.Denotes ε htb fb)
      (aa : Aligned da ha ga) (ab : Aligned db hb gb) :
      Aligned (.let₂ da db) (.let₂ ha hb) (.let₂ ga gb)
  | inl (da : LambdaSSA.Semantics.Monadic.Denotes ε hta fa)
      (a : Aligned da ha ga) : Aligned (.inl da) (.inl ha) (.inl ga)
  | inr (db : LambdaSSA.Semantics.Monadic.Denotes ε htb fb)
      (a : Aligned db hb gb) : Aligned (.inr db) (.inr hb) (.inr gb)
  | case (de : LambdaSSA.Semantics.Monadic.Denotes ε hte fe)
      (dl : LambdaSSA.Semantics.Monadic.Denotes ε htl fl)
      (dr : LambdaSSA.Semantics.Monadic.Denotes ε htr fr)
      (ae : Aligned de he ge) (al : Aligned dl hl gl) (ar : Aligned dr hr gr) :
      Aligned (.case de dl dr) (.case he hl hr) (.case ge gl gr)
  | abort (da : LambdaSSA.Semantics.Monadic.Denotes ε hta fa)
      (a : Aligned da ha ga) : Aligned (.abort da) (.abort ha) (.abort ga)

theorem Aligned.exactGeneric {Γ : LambdaSSA.VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    {ht : LambdaSSA.Tm.HasType Γ t A}
    {f : LambdaSSA.Semantics.Monadic.Env Γ → m (TyDen A)}
    {it : LambdaIter.LocallyNameless.Tm Empty Φ Γ.length}
    {d : LambdaSSA.Semantics.Monadic.Denotes ε ht f}
    {hi : LambdaIter.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ)
      (FromSSA.boundContext Γ) it A}
    {hg : LambdaIter.Subtyping.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ)
      (FromSSA.boundContext Γ) it A}
    (a : Aligned d hi hg) : ExactGeneric hi hg := by
  induction a with
  | var i h e => cases e; exact .bv
  | op _ _ ih => exact .op ih
  | let₁ _ _ _ _ iha ihb => exact .let₁ iha ihb
  | pair _ _ _ _ iha ihb => exact .pair iha ihb
  | unit => exact .unit
  | let₂ _ _ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ _ ih => exact .inl ih
  | inr _ _ ih => exact .inr ih
  | case _ _ _ _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ _ ih => exact .abort ih

theorem Aligned.denotes {Γ : LambdaSSA.VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    {ht : LambdaSSA.Tm.HasType Γ t A}
    {f : LambdaSSA.Semantics.Monadic.Env Γ → m (TyDen A)}
    {it : LambdaIter.LocallyNameless.Tm Empty Φ Γ.length}
    {d : LambdaSSA.Semantics.Monadic.Denotes ε ht f}
    {hi : LambdaIter.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ)
      (FromSSA.boundContext Γ) it A}
    {hg : LambdaIter.Subtyping.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ)
      (FromSSA.boundContext Γ) it A}
    (a : Aligned d hi hg) :
    ∀ ρ, denote (ε := ε) hg PUnit.unit (envToBound ρ) = f ρ := by
  induction a with
  | var i h e =>
      cases e
      intro ρ
      simp only [denote]
      have hv := envToBound_get ρ i h
      have hv' : BoundDen.get (envToBound ρ) i =
          LambdaSSA.Semantics.Monadic.Env.get ρ i h := eq_of_heq hv
      rw [hv']
  | op da a ih => intro ρ; simp only [denote]; rw [ih]
  | let₁ da db aa ab iha ihb =>
      intro ρ; simp only [denote]; rw [iha]
      apply bind_congr; exact fun x => ihb (ρ, x)
  | pair da db aa ab iha ihb =>
      intro ρ; simp only [denote]; rw [iha]
      apply bind_congr; intro x; rw [ihb]
  | unit => intro ρ; simp [denote]
  | let₂ da db aa ab iha ihb =>
      intro ρ; simp only [denote]; rw [iha]
      apply bind_congr
      intro ab
      exact ihb ((ρ, (TypeModel.tensorEquiv _ _ ab).1),
        (TypeModel.tensorEquiv _ _ ab).2)
  | inl da a ih => intro ρ; simp only [denote]; rw [ih]
  | inr da a ih => intro ρ; simp only [denote]; rw [ih]
  | case de dl dr ae al ar ihe ihl ihr =>
      intro ρ; simp only [denote]; rw [ihe]
      apply bind_congr
      intro e
      cases hs : TypeModel.coprodEquiv _ _ e with
      | inl x => exact ihl (ρ, x)
      | inr x => exact ihr (ρ, x)
  | abort da a ih => intro ρ; simp only [denote]; rw [ih]

/-- Specialization of raw constructor alignment to the reconstructed scoped
expression. -/
theorem fromSSA_denotes {Γ : LambdaSSA.VCtx τ} {t : LambdaSSA.Tm Φ} {A : τ}
    {ht : LambdaSSA.Tm.HasType Γ t A}
    {f : LambdaSSA.Semantics.Monadic.Env Γ → m (TyDen A)}
    (s : Scoped Γ.length t)
    {d : LambdaSSA.Semantics.Monadic.Denotes ε ht f}
    {hi : LambdaIter.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ)
      (FromSSA.boundContext Γ) (fromSSA s) A}
    {hg : LambdaIter.Subtyping.LocallyNameless.HasType Φ (Ctx.nil : Ctx Empty τ)
      (FromSSA.boundContext Γ) (fromSSA s) A} (a : Aligned d hi hg) :
    ∀ ρ, denote (ε := ε) hg PUnit.unit (envToBound ρ) = f ρ := a.denotes

end Isotope.LambdaSSA.Translation.Expression.Semantics
