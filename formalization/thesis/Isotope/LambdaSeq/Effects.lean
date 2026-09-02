import Isotope.LambdaSeq.Categorical
import Isotope.LambdaIter.Subtyping.Semantics.Effects

/-!
# Effect soundness for lambda-seq

λ-seq is the straight-line fragment: its denotation needs only a Freyd category, so its effect
soundness needs only the base `EffectModel` — no coproducts, no distributivity, no iteration.
-/

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

namespace Isotope.LambdaSeq

namespace LocallyNameless

variable {ν : Type w} {Φ : Type v} {ε : Type u}

/-- Syntactic effect bound for λ-seq: every instruction occurring in `t` has effect below
`e`. -/
inductive HasEffect [LambdaIter.HasEff Φ ε] [LE ε] (e : ε) :
    {n : Nat} → Tm ν Φ n → Prop where
  | fv : HasEffect e (.fv x)
  | bv : HasEffect e (.bv i)
  | op (hf : LambdaIter.instrEff f ≤ e) (ha : HasEffect e a) : HasEffect e (.op f a)
  | let₁ : HasEffect e a → HasEffect e b → HasEffect e (.let₁ a b)

end LocallyNameless

namespace Semantics.Categorical

open CategoryTheory CategoryTheory.Category
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open Isotope.LambdaIter.Subtyping.Semantics.Categorical.EffectModel
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  {E : Type u₅} [Preorder E] [OrderBot E]
  (J : Functor V C) [FreydCategory J]
  {eff : E → MorphismProperty C} [CategoryTheory.EffectLattice E eff] [EffectModel E J eff]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ] (M : TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ] [LambdaIter.HasEff Φ E] [InstructionModel J M Φ]

/-- Primitive instructions denote morphisms of the effect they declare. -/
class EffectfulInstructionModel : Prop where
  denote_mem (f : Φ) :
    eff (LambdaIter.instrEff f) (InstructionModel.denote (J := J) (M := M) f)

variable [EffectfulInstructionModel J M (eff := eff) (Φ := Φ)]

/-- **Effect soundness for λ-seq.** -/
theorem denote_mem_eff {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LocallyNameless.BoundCtx τ n} {t : LocallyNameless.Tm ν Φ n} {A : τ} {e : E}
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
            (mono_mem hf (EffectfulInstructionModel.denote_mem (eff := eff) _))
  | let₁ ha hb iha ihb =>
      cases he with
      | let₁ hea heb =>
          simp only [denote]
          exact bind_mem (iha hea) (comp_mem (map_mem_eff e _) (ihb heb))

end Semantics.Categorical

namespace Subtyping.Semantics.Categorical

open CategoryTheory CategoryTheory.Category
open CategoryTheory.PremonoidalCategory
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open Isotope.LambdaIter.Subtyping.Semantics.Categorical.EffectModel
open Isotope.LambdaSeq.Semantics.Categorical
open scoped MonoidalCategory

variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  {E : Type u₅} [Preorder E] [OrderBot E]
  (J : Functor V C) [FreydCategory J]
  {eff : E → MorphismProperty C} [CategoryTheory.EffectLattice E eff] [EffectModel E J eff]
  {τ : Type u₃} [LambdaIter.TypeFormers τ] [LambdaIter.Subtyping τ]
  (M : Isotope.LambdaSeq.Semantics.Categorical.TypeModel τ V)
  {ν : Type u₄} [DecidableEq ν]
  {Φ : Type u₄} [LambdaIter.HasTy Φ τ] [LambdaIter.HasEff Φ E]
  [Isotope.LambdaSeq.Semantics.Categorical.InstructionModel J M Φ]
  [Isotope.LambdaSeq.Semantics.Categorical.EffectfulInstructionModel J M (eff := eff) (Φ := Φ)]

/-- **Effect soundness for λ-seq with subtyping.**  Coercions are pure, so a `sub` node does
not change the effect. -/
theorem denote_mem_eff {Γ : LambdaIter.Ctx ν τ} {n : Nat}
    {β : LambdaSeq.LocallyNameless.BoundCtx τ n}
    {t : LambdaSeq.LocallyNameless.Tm ν Φ n} {A : τ} {e : E}
    (h : LocallyNameless.HasType Φ Γ β t A) (he : LambdaSeq.LocallyNameless.HasEffect e t) :
    eff e (denote J M h) := by
  induction h with
  | fv _ => simp only [denote]; exact map_mem_eff e _
  | bv => simp only [denote]; exact map_mem_eff e _
  | op ha ih =>
      cases he with
      | op hf hea =>
          simp only [denote]
          exact comp_mem (ih hea)
            (mono_mem hf
              (Isotope.LambdaSeq.Semantics.Categorical.EffectfulInstructionModel.denote_mem
                (eff := eff) _))
  | let₁ ha hb iha ihb =>
      cases he with
      | let₁ hea heb =>
          simp only [denote]
          exact bind_mem (iha hea) (comp_mem (map_mem_eff e _) (ihb heb))
  | sub ha d ih => simp only [denote]; exact comp_mem (ih he) (map_mem_eff e _)

end Subtyping.Semantics.Categorical

end Isotope.LambdaSeq
