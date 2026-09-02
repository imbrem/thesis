import Isotope.LambdaCase.Semantics.Categorical
import Isotope.LambdaCase.Subtyping.Semantics.Categorical
import Isotope.LambdaIter.Subtyping.Semantics.Effects

/-!
# Effect soundness for lambda-case

λ-case is the branching but loop-free fragment, so its denotation needs only a *distributive*
Freyd category: no `Iteration`, and no Elgot law.  Correspondingly its effect soundness needs
only `EffectModel` and `DistributiveEffectModel`, not `IterativeEffects`.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

namespace Isotope.LambdaCase

namespace LocallyNameless

variable {ν : Type w} {Φ : Type v} {ε : Type u}

/-- Syntactic effect bound for λ-case: every instruction occurring in `t` has effect below
`e`.  There is no iteration to guard. -/
inductive HasEffect [LambdaIter.HasEff Φ ε] [LE ε] (e : ε) :
    {n : Nat} → Tm ν Φ n → Prop where
  | fv : HasEffect e (.fv x)
  | bv : HasEffect e (.bv i)
  | op (hf : LambdaIter.instrEff f ≤ e) (ha : HasEffect e a) : HasEffect e (.op f a)
  | let₁ : HasEffect e a → HasEffect e b → HasEffect e (.let₁ a b)
  | unit : HasEffect e .unit
  | pair : HasEffect e a → HasEffect e b → HasEffect e (.pair a b)
  | let₂ : HasEffect e a → HasEffect e b → HasEffect e (.let₂ a b)
  | inl : HasEffect e a → HasEffect e (.inl a)
  | inr : HasEffect e a → HasEffect e (.inr a)
  | case : HasEffect e c → HasEffect e l → HasEffect e r → HasEffect e (.case c l r)
  | abort : HasEffect e a → HasEffect e (.abort a)

end LocallyNameless

namespace Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open Isotope.LambdaIter.Subtyping.Semantics.Categorical.EffectModel
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {E : Type u₅} [Preorder E] [OrderBot E]
  (J : Functor V C) [DistributiveFreydCategory J]
  {eff : E → MorphismProperty C} [CategoryTheory.EffectLattice E eff]
  [EffectModel E J eff] [DistributiveEffectModel E J eff]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ] [LambdaIter.HasEff Φ E] [InstructionModel J M Φ]
  [EffectfulInstructionModel E J eff M Φ]

/-- **Effect soundness for λ-case.** -/
theorem denote_mem_eff {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {t : LocallyNameless.Tm ν Φ n} {A : τ} {e : E}
    (h : LocallyNameless.HasType Φ Γ β t A) (he : LocallyNameless.HasEffect e t) :
    eff e (denote J M h) := by
  induction h with
  | fv _ => simp only [denote]; exact map_mem_eff e _
  | bv => simp only [denote]; exact map_mem_eff e _
  | op ha ih =>
      cases he with
      | op hf hea =>
          simp only [denote]
          exact comp_mem (ih hea)
            (mono_mem hf (EffectfulInstructionModel.denote_mem (E := E) (J := J) (M := M) _))
  | let₁ ha hb iha ihb =>
      cases he with
      | let₁ hea heb =>
          simp only [denote]
          exact bind_mem (iha hea) (comp_mem (map_mem_eff e _) (ihb heb))
  | unit => simp only [denote]; exact map_mem_eff e _
  | pair ha hb iha ihb =>
      cases he with
      | pair hea heb =>
          simp only [denote]
          exact comp_mem (pair_mem (iha hea) (ihb heb)) (map_mem_eff e _)
  | let₂ ha hc iha ihc =>
      cases he with
      | let₂ hea hec =>
          simp only [denote]
          exact bind_mem (iha hea)
            (comp_mem (map_mem_eff e _) (comp_mem (map_mem_eff e _) (ihc hec)))
  | inl ha ih =>
      cases he with
      | inl hea => simp only [denote]; exact comp_mem (ih hea) (map_mem_eff e _)
  | inr hb ih =>
      cases he with
      | inr heb => simp only [denote]; exact comp_mem (ih heb) (map_mem_eff e _)
  | case hc hl hr ihc ihl ihr =>
      cases he with
      | case hec hel her =>
          simp only [denote]
          exact caseWithContext_mem (comp_mem (ihc hec) (map_mem_eff e _))
            (comp_mem (map_mem_eff e _) (ihl hel))
            (comp_mem (map_mem_eff e _) (ihr her))
  | abort ha ih =>
      cases he with
      | abort hea => simp only [denote]; exact abort_mem M (ih hea)

end Semantics.Categorical

namespace Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open Isotope.LambdaIter.Subtyping.Semantics.Categorical.EffectModel
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  {E : Type u₅} [Preorder E] [OrderBot E]
  (J : Functor V C) [DistributiveFreydCategory J]
  {eff : E → MorphismProperty C} [CategoryTheory.EffectLattice E eff]
  [EffectModel E J eff] [DistributiveEffectModel E J eff]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ] [LambdaIter.HasEff Φ E] [InstructionModel J M Φ]
  [EffectfulInstructionModel E J eff M Φ]

/-- **Effect soundness for λ-case with subtyping.**  Coercions are pure, so a `sub` node does
not change the effect. -/
theorem denote_mem_eff {Γ : Ctx ν τ} {n : Nat} {β : LocallyNameless.BoundCtx τ n}
    {t : LambdaCase.LocallyNameless.Tm ν Φ n} {A : τ} {e : E}
    (h : LocallyNameless.HasType Φ Γ β t A) (he : LambdaCase.LocallyNameless.HasEffect e t) :
    eff e (denote J M h) := by
  induction h with
  | fv _ => simp only [denote]; exact map_mem_eff e _
  | bv => simp only [denote]; exact map_mem_eff e _
  | op ha ih =>
      cases he with
      | op hf hea =>
          simp only [denote]
          exact comp_mem (ih hea)
            (mono_mem hf (EffectfulInstructionModel.denote_mem (E := E) (J := J) (M := M) _))
  | let₁ ha hb iha ihb =>
      cases he with
      | let₁ hea heb =>
          simp only [denote]
          exact bind_mem (iha hea) (comp_mem (map_mem_eff e _) (ihb heb))
  | unit => simp only [denote]; exact map_mem_eff e _
  | pair ha hb iha ihb =>
      cases he with
      | pair hea heb =>
          simp only [denote]
          exact comp_mem (pair_mem (iha hea) (ihb heb)) (map_mem_eff e _)
  | let₂ ha hc iha ihc =>
      cases he with
      | let₂ hea hec =>
          simp only [denote]
          exact bind_mem (iha hea)
            (comp_mem (map_mem_eff e _) (comp_mem (map_mem_eff e _) (ihc hec)))
  | inl ha ih =>
      cases he with
      | inl hea => simp only [denote]; exact comp_mem (ih hea) (map_mem_eff e _)
  | inr hb ih =>
      cases he with
      | inr heb => simp only [denote]; exact comp_mem (ih heb) (map_mem_eff e _)
  | case hc hl hr ihc ihl ihr =>
      cases he with
      | case hec hel her =>
          simp only [denote]
          exact caseWithContext_mem (comp_mem (ihc hec) (map_mem_eff e _))
            (comp_mem (map_mem_eff e _) (ihl hel))
            (comp_mem (map_mem_eff e _) (ihr her))
  | abort ha ih =>
      cases he with
      | abort hea => simp only [denote]; exact abort_mem M (ih hea)
  | sub ha d ih => simp only [denote]; exact comp_mem (ih he) (map_mem_eff e _)

end Subtyping.Semantics.Categorical

end Isotope.LambdaCase
