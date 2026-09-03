import Isotope.LambdaIter.Semantics.Categorical

/-!
# Clause-by-clause equations for the exact categorical denotation

`LocallyNameless.Categorical.denote` is the generic categorical denotation
composed with `HasType.toGeneric`.  These are its twelve defining equations,
read off directly, so that structural inductions over exact derivations need
not unfold the embedding by hand.
-/

namespace Isotope.LambdaIter.LocallyNameless.Categorical

universe v₁ v₂ u₁ u₂ u₃ u₄ u₅

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.Subtyping.Semantics.Categorical
open scoped MonoidalCategory

variable {τ : Type u₃} [TypeFormers τ] [Subtyping τ]
variable {ν : Type u₄} [DecidableEq ν]
variable {Φ : Type u₅} [HasTy Φ τ]
variable {V : Type u₁} {C : Type u₂}
  [Category.{v₁} V] [Category.{v₂} C]
  [CartesianMonoidalCategory V] [SymmetricCategory V]
  [PremonoidalCategory C] [SymmetricPremonoidalCategory C]
  [HasFiniteCoproducts V] [HasFiniteCoproducts C]
  [DistributiveTensor V] [DistributivePremonoidalCategory C]
  [Iteration C] [ElgotCategory C]
  (J : Functor V C) [StrongElgotFreydCategory J]
  (M : TypeModel τ V) [InstructionModel J M Φ]
  {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

/-- The free-variable clause. -/
@[simp] theorem denote_fv {x : ν} {A : τ} (hx : Γ.lookup x = some A) :
    denote J M (HasType.fv (Φ := Φ) (β := β) hx) = J.map (freeLookup M x hx) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]

/-- The bound-variable clause. -/
@[simp] theorem denote_bv {i : Fin n} :
    denote J M (HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := i)) =
      J.map (boundVar M i) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]

/-- The instruction clause. -/
@[simp] theorem denote_op {a : Tm ν Φ n} {f : Φ}
    (ha : HasType Φ Γ β a (instrSrc f)) :
    denote J M (HasType.op ha) =
      denote J M ha ≫ InstructionModel.denote (J := J) (M := M) f := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]

/-- The `let` clause. -/
@[simp] theorem denote_let₁ {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B) :
    denote J M (HasType.let₁ ha hb) =
      bind J (denote J M ha)
        (J.map (envSnocIso M Γ β A).hom ≫ denote J M hb) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]

/-- The unit clause. -/
@[simp] theorem denote_unit :
    denote J M (HasType.unit (Φ := Φ) (Γ := Γ) (β := β)) =
      J.map (CartesianMonoidalCategory.toUnit _ ≫ M.unitIso.inv) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]
  rfl

/-- The pairing clause. -/
@[simp] theorem denote_pair {a b : Tm ν Φ n} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
    denote J M (HasType.pair ha hb) =
      pair J (denote J M ha) (denote J M hb) ≫ J.map (M.tensorIso A B).inv := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]
  rfl

/-- The pair-elimination clause. -/
@[simp] theorem denote_let₂ {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B D : τ}
    (ha : HasType Φ Γ β a (TypeFormers.tensor A B))
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c D) :
    denote J M (HasType.let₂ ha hc) =
      bind J (denote J M ha)
        (J.map ((𝟙 _) ⊗ₘ (M.tensorIso A B).hom) ≫
          J.map (envPairHom M Γ β A B) ≫ denote J M hc) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]
  rfl

/-- The left-injection clause. -/
@[simp] theorem denote_inl {a : Tm ν Φ n} {A B : τ}
    (ha : HasType Φ Γ β a A) :
    denote J M (HasType.inl (B := B) ha) =
      denote J M ha ≫ J.map (coprod.inl ≫ (M.coprodIso A B).inv) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]
  rfl

/-- The right-injection clause. -/
@[simp] theorem denote_inr {b : Tm ν Φ n} {A B : τ}
    (hb : HasType Φ Γ β b B) :
    denote J M (HasType.inr (A := A) hb) =
      denote J M hb ≫ J.map (coprod.inr ≫ (M.coprodIso A B).inv) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]
  rfl

/-- The case clause. -/
@[simp] theorem denote_case {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B D : τ}
    (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (hl : HasType Φ Γ (.snoc β A) l D) (hr : HasType Φ Γ (.snoc β B) r D) :
    denote J M (HasType.case he hl hr) =
      caseWithContext J (denote J M he ≫ J.map (M.coprodIso A B).hom)
        (J.map (envSnocIso M Γ β A).hom ≫ denote J M hl)
        (J.map (envSnocIso M Γ β B).hom ≫ denote J M hr) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]
  rfl

/-- The `abort` clause. -/
@[simp] theorem denote_abort {a : Tm ν Φ n} {D : τ}
    (ha : HasType Φ Γ β a (TypeFormers.empty : τ)) :
    denote J M (HasType.abort (C := D) ha) =
      abort J M (A := D) (denote J M ha) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]
  rfl

/-- The iteration clause. -/
@[simp] theorem denote_iter {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A)) :
    denote J M (HasType.iter ha hb) =
      bind J (denote J M ha)
        (contextualLoop J (J.map (envSnocIso M Γ β A).hom ≫ denote J M hb ≫
          J.map (M.coprodIso B A).hom)) := by
  simp only [denote, HasType.toGeneric,
    Isotope.LambdaIter.Subtyping.Semantics.Categorical.denote]
  rfl

end Isotope.LambdaIter.LocallyNameless.Categorical
