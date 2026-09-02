import Isotope.LambdaCase.Metatheory.Syntax

/-!
# De Bruijn identities about shifting binders in one-variable terms

These are the raw-syntax content of the category laws and the coproduct laws of
the one-variable syntactic category (`Isotope/LambdaCase/Models/SynCategory.lean`
and `.../SynCoproduct.lean`).

Every one of them is proved by transport along the injective `Tm.embed`, from a
private lambda-iter counterpart stated and proved here.  Those counterparts are
deliberately kept `private` and inside the lambda-case namespace: identical
lambda-iter-level lemmas are being added concurrently by another development,
and duplicating them in `Isotope.LambdaIter.LocallyNameless.Tm` would be a
silent double definition rather than an obvious conflict.
-/

namespace Isotope.LambdaCase.LocallyNameless

variable {ν : Type w} {Φ : Type v} {n : Nat}

section IterHelpers

open Isotope.LambdaIter.LocallyNameless.Syntax
open Isotope.LambdaIter.LocallyNameless (Tm) in
private theorem iterInstUnder (t : LambdaIter.LocallyNameless.Tm ν Φ (n + 1)) :
    LambdaIter.LocallyNameless.Tm.instantiate
      (LambdaIter.LocallyNameless.Tm.underBinder t) (.bv 0) = t := by
  simp only [LambdaIter.LocallyNameless.Tm.underBinder,
    LambdaIter.LocallyNameless.Tm.instantiate, bsubst_rename]
  rw [bsubst_congr
    (σ' := fun i => (LambdaIter.LocallyNameless.Tm.bv i : _))
    (fun i => by refine Fin.cases rfl (fun _ => rfl) i)]
  rw [bsubst_bv_eq_rename, rename_id]

private theorem iterUnderLet (b c : LambdaIter.LocallyNameless.Tm ν Φ 1) :
    LambdaIter.LocallyNameless.Tm.underBinder
        (.let₁ b (LambdaIter.LocallyNameless.Tm.underBinder c)) =
      .let₁ (LambdaIter.LocallyNameless.Tm.underBinder b)
        (LambdaIter.LocallyNameless.Tm.underBinder
          (LambdaIter.LocallyNameless.Tm.underBinder c)) := by
  rw [LambdaIter.LocallyNameless.Tm.underBinder, rename_let₁]
  congr 1
  simp only [LambdaIter.LocallyNameless.Tm.underBinder, rename_comp]
  exact rename_congr (fun i => by refine Fin.cases rfl (fun j => j.elim0) i) c

private theorem iterRenameEqOfZero {m : Nat} (ρ ρ' : Fin 1 → Fin m)
    (h : ρ 0 = ρ' 0) (c : LambdaIter.LocallyNameless.Tm ν Φ 1) :
    LambdaIter.LocallyNameless.Tm.rename ρ c =
      LambdaIter.LocallyNameless.Tm.rename ρ' c :=
  rename_congr (fun i => by refine Fin.cases h (fun j => j.elim0) i) c

private theorem iterBsubstEqRenameOfZero {m : Nat}
    (σ : Fin 1 → LambdaIter.LocallyNameless.Tm ν Φ m) (ρ : Fin 1 → Fin m)
    (h : σ 0 = .bv (ρ 0)) (c : LambdaIter.LocallyNameless.Tm ν Φ 1) :
    LambdaIter.LocallyNameless.Tm.bsubst σ c =
      LambdaIter.LocallyNameless.Tm.rename ρ c := by
  rw [bsubst_congr
    (σ' := fun i => (LambdaIter.LocallyNameless.Tm.bv (ρ i) : _))
    (fun i => by refine Fin.cases h (fun j => j.elim0) i)]
  exact bsubst_bv_eq_rename ρ c

private theorem iterRenameUpUnder (ρ : Fin 1 → Fin 2)
    (c : LambdaIter.LocallyNameless.Tm ν Φ 1) :
    LambdaIter.LocallyNameless.Tm.rename (upRen ρ)
        (LambdaIter.LocallyNameless.Tm.underBinder c) =
      LambdaIter.LocallyNameless.Tm.underBinder
        (LambdaIter.LocallyNameless.Tm.underBinder c) := by
  simp only [LambdaIter.LocallyNameless.Tm.underBinder, rename_comp]
  refine iterRenameEqOfZero _ _ ?_ c
  rfl

private theorem iterBsubstUpUnder
    (σ : Fin 2 → LambdaIter.LocallyNameless.Tm ν Φ 1)
    (c : LambdaIter.LocallyNameless.Tm ν Φ 1) :
    LambdaIter.LocallyNameless.Tm.bsubst (upSub σ)
        (LambdaIter.LocallyNameless.Tm.underBinder
          (LambdaIter.LocallyNameless.Tm.underBinder c)) =
      LambdaIter.LocallyNameless.Tm.underBinder c := by
  simp only [LambdaIter.LocallyNameless.Tm.underBinder, bsubst_rename]
  refine iterBsubstEqRenameOfZero _ _ ?_ c
  rfl

private theorem iterInstCaseInl (l r : LambdaIter.LocallyNameless.Tm ν Φ 1) :
    LambdaIter.LocallyNameless.Tm.instantiate
        ((LambdaIter.LocallyNameless.Tm.bv 0).case
          (LambdaIter.LocallyNameless.Tm.underBinder
            (LambdaIter.LocallyNameless.Tm.underBinder l))
          (LambdaIter.LocallyNameless.Tm.underBinder
            (LambdaIter.LocallyNameless.Tm.underBinder r)))
        ((LambdaIter.LocallyNameless.Tm.bv 0).inl) =
      ((LambdaIter.LocallyNameless.Tm.bv 0).inl).case
        (LambdaIter.LocallyNameless.Tm.underBinder l)
        (LambdaIter.LocallyNameless.Tm.underBinder r) :=
  congrArg₂
    (fun x y : LambdaIter.LocallyNameless.Tm ν Φ 2 =>
      ((LambdaIter.LocallyNameless.Tm.bv 0).inl).case x y)
    (iterBsubstUpUnder _ l) (iterBsubstUpUnder _ r)

private theorem iterInstCaseInr (l r : LambdaIter.LocallyNameless.Tm ν Φ 1) :
    LambdaIter.LocallyNameless.Tm.instantiate
        ((LambdaIter.LocallyNameless.Tm.bv 0).case
          (LambdaIter.LocallyNameless.Tm.underBinder
            (LambdaIter.LocallyNameless.Tm.underBinder l))
          (LambdaIter.LocallyNameless.Tm.underBinder
            (LambdaIter.LocallyNameless.Tm.underBinder r)))
        ((LambdaIter.LocallyNameless.Tm.bv 0).inr) =
      ((LambdaIter.LocallyNameless.Tm.bv 0).inr).case
        (LambdaIter.LocallyNameless.Tm.underBinder l)
        (LambdaIter.LocallyNameless.Tm.underBinder r) :=
  congrArg₂
    (fun x y : LambdaIter.LocallyNameless.Tm ν Φ 2 =>
      ((LambdaIter.LocallyNameless.Tm.bv 0).inr).case x y)
    (iterBsubstUpUnder _ l) (iterBsubstUpUnder _ r)

end IterHelpers

namespace Tm

/-- Opening the binder introduced by `underBinder` with the variable it
displaced is the identity.  This is the de Bruijn content of `𝟙 ≫ g = g` in
the one-variable syntactic category. -/
theorem instantiate_underBinder_bv_zero (t : Tm ν Φ (n + 1)) :
    Tm.instantiate (Tm.underBinder t) (.bv 0) = t :=
  Tm.embed_injective (by simpa [Tm.embed] using iterInstUnder (Tm.embed t))

/-- Shifting a `let` whose body is already shifted.  The two renamings agree
because their common domain is `Fin 1`: this is the de Bruijn content of
associativity of composition in the one-variable syntactic category. -/
theorem underBinder_let₁_underBinder (b c : Tm ν Φ 1) :
    Tm.underBinder (.let₁ b (Tm.underBinder c)) =
      .let₁ (Tm.underBinder b) (Tm.underBinder (Tm.underBinder c)) :=
  Tm.embed_injective
    (by simpa [Tm.embed] using iterUnderLet (Tm.embed b) (Tm.embed c))

/-- Shifting under an extra binder a one-variable term that is already
shifted.  The two renamings agree because their common domain is `Fin 1`. -/
theorem rename_upRen_underBinder (ρ : Fin 1 → Fin 2) (c : Tm ν Φ 1) :
    Tm.rename (LambdaIter.LocallyNameless.Syntax.upRen ρ) (Tm.underBinder c) =
      Tm.underBinder (Tm.underBinder c) :=
  Tm.embed_injective (by simpa using iterRenameUpUnder ρ (Tm.embed c))

/-- Shifting a `case` on the bound variable whose branches are already
shifted. -/
theorem underBinder_case_underBinder (l r : Tm ν Φ 1) :
    Tm.underBinder ((Tm.bv 0).case (Tm.underBinder l) (Tm.underBinder r)) =
      (Tm.bv 0).case (Tm.underBinder (Tm.underBinder l))
        (Tm.underBinder (Tm.underBinder r)) :=
  congrArg₂ (fun x y : Tm ν Φ 3 => (Tm.bv 0).case x y)
    (rename_upRen_underBinder _ l) (rename_upRen_underBinder _ r)

/-- Opening the `case` redex produced by `injl ≫ desc l r`. -/
theorem instantiate_case_inl (l r : Tm ν Φ 1) :
    Tm.instantiate
        ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder l))
          (Tm.underBinder (Tm.underBinder r)))
        ((Tm.bv 0).inl) =
      ((Tm.bv 0).inl).case (Tm.underBinder l) (Tm.underBinder r) :=
  Tm.embed_injective
    (by simpa [Tm.embed] using iterInstCaseInl (Tm.embed l) (Tm.embed r))

/-- Opening the `case` redex produced by `injr ≫ desc l r`. -/
theorem instantiate_case_inr (l r : Tm ν Φ 1) :
    Tm.instantiate
        ((Tm.bv 0).case (Tm.underBinder (Tm.underBinder l))
          (Tm.underBinder (Tm.underBinder r)))
        ((Tm.bv 0).inr) =
      ((Tm.bv 0).inr).case (Tm.underBinder l) (Tm.underBinder r) :=
  Tm.embed_injective
    (by simpa [Tm.embed] using iterInstCaseInr (Tm.embed l) (Tm.embed r))

end Tm

end Isotope.LambdaCase.LocallyNameless
