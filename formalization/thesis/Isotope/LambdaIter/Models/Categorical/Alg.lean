import Isotope.LambdaIter.Models.Categorical.Denotation
import Isotope.LambdaIter.Models.Alg
import Isotope.LambdaIter.Semantics.Soundness

/-!
# A Freyd-categorical model is an algebra of the lambda-iter presentation

`Models/Alg.lean` records that nothing in the repository turns a Freyd category
into an object of `Alg S`, "which would require discharging `coh` and `sound`
in the category, which is exactly the work those two missing instances
represent".  This file does exactly that, taking the two classes as hypotheses;
`Isotope/LambdaIter/Semantics/Kleisli/Model.lean` supplies them at the Kleisli
model, so the construction is not vacuous.

The only extra hypothesis is `[Subtyping S.Ty]`: a `Sig` deliberately carries
no subtyping structure, while the categorical `TypeModel` interface is stated
for a type universe that has some.  The freely generated `Ty α` has one, which
is where the concrete models live.
-/

namespace Isotope.LambdaIter.Categorical

open LocallyNameless
open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open scoped MonoidalCategory

universe u v₁ v₂ u₁ u₂

variable {S : Sig.{u}} [Subtyping S.Ty]
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  (M : TypeModel S.Ty V) [InstructionModel J M S.Instr]

/-- The operations of a Freyd-categorical model: the clauses of
`LocallyNameless.Categorical.denote` at the empty free context, read as
operations on computation morphisms out of the environment object. -/
noncomputable def ops : Alg.Ops.{u, v₂} S where
  El β A :=
    J.obj (envObj M (Ctx.nil : Ctx Empty S.Ty) β) ⟶ J.obj (M.obj A)
  var i := J.map (boundVar M i)
  op f x := x ≫ InstructionModel.denote (J := J) (M := M) f
  let₁ x y := bind J x (J.map (envSnocIso M Ctx.nil _ _).hom ≫ y)
  unit := J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv)
  pair x y := pair J x y ≫ J.map (M.tensorIso _ _).inv
  let₂ x y := bind J x (J.map ((𝟙 _) ⊗ₘ (M.tensorIso _ _).hom) ≫
    J.map (envPairHom M Ctx.nil _ _ _) ≫ y)
  inl x := x ≫ J.map (coprod.inl ≫ (M.coprodIso _ _).inv)
  inr x := x ≫ J.map (coprod.inr ≫ (M.coprodIso _ _).inv)
  case e l r := caseWithContext J (e ≫ J.map (M.coprodIso _ _).hom)
    (J.map (envSnocIso M Ctx.nil _ _).hom ≫ l)
    (J.map (envSnocIso M Ctx.nil _ _).hom ≫ r)
  abort x := abort J M x
  iter x y := bind J x (contextualLoop J
    (J.map (envSnocIso M Ctx.nil _ _).hom ≫ y ≫ J.map (M.coprodIso _ _).hom))

/-- The interpretation of a derivation by `ops` is the categorical
denotation. -/
theorem ops_denote {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n}
    {A : S.Ty} (h : HasType S.Instr Ctx.nil β t A) :
    (ops J M).denote h = LocallyNameless.Categorical.denote J M h := by
  induction h with
  | fv h => exact absurd h (by simp [LambdaIter.Ctx.lookup])
  | bv => simp only [Alg.Ops.denote_bv, LocallyNameless.Categorical.denote_bv]; rfl
  | op h ih =>
      rw [Alg.Ops.denote_op, LocallyNameless.Categorical.denote_op, ih]
      rfl
  | let₁ ha hb iha ihb =>
      rw [Alg.Ops.denote_let₁, LocallyNameless.Categorical.denote_let₁,
        iha, ihb]
      rfl
  | unit => simp only [Alg.Ops.denote_unit, LocallyNameless.Categorical.denote_unit]; rfl
  | pair ha hb iha ihb =>
      rw [Alg.Ops.denote_pair, LocallyNameless.Categorical.denote_pair,
        iha, ihb]
      rfl
  | let₂ ha hc iha ihc =>
      rw [Alg.Ops.denote_let₂, LocallyNameless.Categorical.denote_let₂,
        iha, ihc]
      rfl
  | inl ha ih =>
      rw [Alg.Ops.denote_inl, LocallyNameless.Categorical.denote_inl, ih]
      rfl
  | inr hb ih =>
      rw [Alg.Ops.denote_inr, LocallyNameless.Categorical.denote_inr, ih]
      rfl
  | case he hl hr ihe ihl ihr =>
      rw [Alg.Ops.denote_case, LocallyNameless.Categorical.denote_case,
        ihe, ihl, ihr]
      rfl
  | abort ha ih =>
      rw [Alg.Ops.denote_abort, LocallyNameless.Categorical.denote_abort, ih]
      rfl
  | iter ha hb iha ihb =>
      rw [Alg.Ops.denote_iter, LocallyNameless.Categorical.denote_iter,
        iha, ihb]
      rfl

variable [LocallyNameless.Categorical.TypingCoherent (τ := S.Ty) (ν := Empty)
    (Φ := S.Instr) J M]
  [LocallyNameless.Categorical.LawfulModel (τ := S.Ty) (ν := Empty)
    (Φ := S.Instr) (ε := S.Eff) (pureEff := S.pureEff) J M]

/-- **A Freyd-categorical model is an algebra of the presentation.**  Both
propositional fields of `Alg` are discharged from the two categorical coherence
classes: `coh` is `TypingCoherent`, and `sound` is
`LocallyNameless.Categorical.sound_between`, whose whole congruence induction
was already proved from those classes. -/
noncomputable def _root_.Isotope.LambdaIter.Alg.ofCategorical :
    Alg.{u, v₂} S where
  toOps := ops J M
  coh h k := by
    rw [ops_denote, ops_denote]
    exact LocallyNameless.Categorical.TypingCoherent.denote_eq h k
  sound h k he := by
    rw [ops_denote, ops_denote]
    exact LocallyNameless.Categorical.sound_between J M he h k

/-- The denotation in `Alg.ofCategorical` is the categorical denotation. -/
@[simp] theorem ofCategorical_denote {n : Nat} {β : BoundCtx S.Ty n}
    {t : Tm Empty S.Instr n} {A : S.Ty}
    (h : HasType S.Instr Ctx.nil β t A) :
    (Alg.ofCategorical J M).denote h =
      LocallyNameless.Categorical.denote J M h := ops_denote J M h

end Isotope.LambdaIter.Categorical
