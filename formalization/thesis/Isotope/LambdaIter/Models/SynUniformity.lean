import Isotope.LambdaIter.Models.SynIteration

/-!
# Pure morphisms and the uniformity law

The last of the four equational Elgot laws is **uniformity**, and unlike the
other three it is not a bare equation: it holds only for transports along
*pure* morphisms.

## What "pure" can mean here

Syntactic purity of raw terms is **not** stable under `Eqv`: the axiom
`StructuralAxiom.emptyInitial` relates `let₁ (abort a) b` to
`let₁ (abort a) c` for an arbitrary `c`, so a pure term is provably equal to an
impure one.  A predicate on classes therefore cannot be "the representative is
pure".  What does work is the existential

```
IsPureMor f  ↔  some representative of f is syntactically pure
```

which is stable by construction.  It contains the identity and is closed under
composition, so the pure morphisms form a wide subcategory of the syntactic
category.  That is the honest replacement, in this development, for the value
fragment of a Freyd category.

## Honest boundary

* `IsPureMor` is closed under identity and composition, but **no claim is made
  that it is cartesian**, or that it is the image of a value category under a
  Freyd functor, or that the syntactic category is premonoidal over it.  It is
  a wide subcategory and nothing more.
* Uniformity is proved in the equational form the syntactic axiom supplies.  It
  is *not* stated as `ElgotFreydCategory.uniformity`, which quantifies over
  morphisms of an ambient value category `V` and a functor `J`; no such Freyd
  structure exists here.
* Strength (`StrongElgotFreydCategory.iterate_whiskerLeft`) remains out of
  reach and cannot even be stated: it needs premonoidal and distributive
  structure, which this development does not build.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory

universe u w q

namespace LocallyNameless.Tm

variable {ν : Type w} {Φ : Type q}

/-- Normal form of the body of `f ≫ desc injl (k ≫ injr)`. -/
theorem underBinder_desc_inr (c : Tm ν Φ 1) :
    Tm.underBinder ((Tm.bv 0).case (Tm.underBinder ((Tm.bv 0).inl))
        (Tm.underBinder (Tm.let₁ c (Tm.underBinder ((Tm.bv 0).inr))))) =
      (Tm.bv 0).case ((Tm.bv 0).inl)
        (Tm.let₁ (Tm.underBinder (Tm.underBinder c)) ((Tm.bv 0).inr)) :=
  congrArg (fun x : Tm ν Φ 3 =>
      (Tm.bv 0).case ((Tm.bv 0).inl) (Tm.let₁ x ((Tm.bv 0).inr)))
    (rename_upRen_underBinder _ c)

/-- Shifting the normalized square once more. -/
theorem underBinder_square (b c : Tm ν Φ 1) :
    Tm.underBinder (Tm.let₁ b
        ((Tm.bv 0).case ((Tm.bv 0).inl)
          (Tm.let₁ (Tm.underBinder (Tm.underBinder c)) ((Tm.bv 0).inr)))) =
      Tm.let₁ (Tm.underBinder b)
        ((Tm.bv 0).case ((Tm.bv 0).inl)
          (Tm.let₁ (Tm.underBinder (Tm.underBinder (Tm.underBinder c)))
            ((Tm.bv 0).inr))) :=
  congrArg (fun x : Tm ν Φ 4 =>
      Tm.let₁ (Tm.underBinder b)
        ((Tm.bv 0).case ((Tm.bv 0).inl) (Tm.let₁ x ((Tm.bv 0).inr))))
    (rename_upRen_underBinder₂ _ c)

/-- Shifting a `let` whose body is a shifted one-variable term. -/
theorem underBinder_let₁_shift (b c : Tm ν Φ 1) :
    Tm.underBinder (Tm.let₁ b (Tm.underBinder c)) =
      Tm.let₁ (Tm.underBinder b) (Tm.underBinder (Tm.underBinder c)) :=
  congrArg (fun x : Tm ν Φ 3 => Tm.let₁ (Tm.underBinder b) x)
    (rename_upRen_underBinder _ c)

end LocallyNameless.Tm

namespace Syn.SynCat

variable {S : Sig.{u}}

/-- A morphism of the syntactic category is **pure** when some representative
of it is a syntactically pure term.

The existential is essential: raw purity is not stable under `Eqv` (see the
module docstring), so "the representative is pure" is not well defined on
classes. -/
def IsPureMor {A B : SynCat S} (f : A ⟶ B) : Prop :=
  ∃ (t : Tm Empty S.Instr 1)
    (h : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty) t B.ty),
    Pure S.pureEff t ∧ mk h = f

/-- The identity is pure. -/
theorem isPureMor_id (A : SynCat S) : IsPureMor (𝟙 A) :=
  ⟨.bv 0, HasType.newest, Pure.bv, rfl⟩

/-- Pure morphisms are closed under composition. -/
theorem IsPureMor.comp {A B C : SynCat S} {f : A ⟶ B} {g : B ⟶ C}
    (hf : IsPureMor f) (hg : IsPureMor g) : IsPureMor (f ≫ g) := by
  obtain ⟨tf, hft, hfp, rfl⟩ := hf
  obtain ⟨tg, hgt, hgp, rfl⟩ := hg
  exact ⟨_, HasType.let₁ hft hgt.underBinder,
    Pure.let₁ hfp (hgp.rename _), rfl⟩

/-- **The uniformity law.**  If a pure morphism `k` transports the loop body of
`f` to that of `f'`, then it transports the whole iteration.

This is the fourth Elgot law, in the equational form the syntactic axiom
supplies; see the module docstring for what it is not. -/
theorem iterate_uniformity {A A' B : SynCat S}
    (f : A ⟶ cop B A) (f' : A' ⟶ cop B A') (k : A ⟶ A') (hk : IsPureMor k)
    (square : f ≫ desc (injl B A') (k ≫ injr B A') = k ≫ f') :
    iterate f = k ≫ iterate f' := by
  obtain ⟨tk, htk, hpk, rfl⟩ := hk
  induction f using Syn.ind with
  | H tf hf =>
    induction f' using Syn.ind with
    | H tf' hf' =>
      -- shifted copies of the three terms
      have hf1 := hf.underBinder (X := A.ty)
      have hf'1 := hf'.underBinder (X := A.ty)
      have hf'2 := hf'1.underBinder (X := A.ty)
      have hf'2b := hf'1.underBinder (X := A'.ty)
      have hk1 := htk.underBinder (X := A.ty)
      have hk2 := hk1.underBinder (X := A.ty)
      have hk2' := hk1.underBinder (X := LambdaIter.coprod B.ty A.ty)
      have hk3 := hk2.underBinder (X := LambdaIter.coprod B.ty A.ty)
      have hpk1 : Pure S.pureEff (Tm.underBinder tk) := hpk.rename _
      -- the hypothesis, with its body normalized
      have hsq : Eqv (Φ := S.Instr) S.pureEff Ctx.nil
          (BoundCtx.nil.snoc A.ty)
          (Tm.let₁ tf (Tm.underBinder ((Tm.bv 0).case
            (Tm.underBinder ((Tm.bv 0).inl))
            (Tm.underBinder (Tm.let₁ tk (Tm.underBinder ((Tm.bv 0).inr)))))))
          (Tm.let₁ tk (Tm.underBinder tf'))
          (LambdaIter.coprod B.ty A'.ty) := Quotient.exact square
      rw [Tm.underBinder_desc_inr] at hsq
      -- shift the hypothesis under the loop binder
      have hsq1 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          (Tm.underBinder (Tm.let₁ tf
            ((Tm.bv 0).case ((Tm.bv 0).inl)
              (Tm.let₁ (Tm.underBinder (Tm.underBinder tk))
                ((Tm.bv 0).inr)))))
          (Tm.underBinder (Tm.let₁ tk (Tm.underBinder tf')))
          (LambdaIter.coprod B.ty A'.ty) :=
        Eqv.rename (TypedRenaming.underBinder BoundCtx.nil A.ty A.ty) hsq
      rw [Tm.underBinder_square, Tm.underBinder_let₁_shift] at hsq1
      -- assemble the square required by `Eqv.uniformity`
      have hcase : HasType S.Instr Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          ((Tm.underBinder tf).case ((Tm.bv 0).inl)
            ((Tm.underBinder (Tm.underBinder tk)).inr))
          (LambdaIter.coprod B.ty A'.ty) :=
        HasType.case (A := B.ty) (B := A.ty) hf1
          (HasType.inl (B := A'.ty) HasType.newest)
          (HasType.inr (A := B.ty) hk2)
      have hbind : HasType S.Instr Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          (Tm.let₁ (Tm.underBinder tf)
            ((Tm.bv 0).case ((Tm.bv 0).inl)
              ((Tm.underBinder (Tm.underBinder (Tm.underBinder tk))).inr)))
          (LambdaIter.coprod B.ty A'.ty) :=
        HasType.let₁ hf1
          (HasType.case (A := B.ty) (B := A.ty) HasType.newest
            (HasType.inl (B := A'.ty) HasType.newest)
            (HasType.inr (A := B.ty) hk3))
      have hbind' : HasType S.Instr Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          (Tm.let₁ (Tm.underBinder tf)
            ((Tm.bv 0).case ((Tm.bv 0).inl)
              (Tm.let₁ (Tm.underBinder (Tm.underBinder (Tm.underBinder tk)))
                ((Tm.bv 0).inr))))
          (LambdaIter.coprod B.ty A'.ty) :=
        HasType.let₁ hf1
          (HasType.case (A := B.ty) (B := A.ty) HasType.newest
            (HasType.inl (B := A'.ty) HasType.newest)
            (HasType.let₁ hk3 (HasType.inr (A := B.ty) HasType.newest)))
      have hlet : HasType S.Instr Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          (Tm.let₁ (Tm.underBinder tk)
            (Tm.underBinder (Tm.underBinder tf')))
          (LambdaIter.coprod B.ty A'.ty) := HasType.let₁ hk1 hf'2
      have hinst : HasType S.Instr Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          (Tm.instantiate (Tm.underBinder (Tm.underBinder tf'))
            (Tm.underBinder tk))
          (LambdaIter.coprod B.ty A'.ty) := HasType.instantiate hf'2 hk1
      have s1 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          ((Tm.underBinder tf).case ((Tm.bv 0).inl)
            ((Tm.underBinder (Tm.underBinder tk)).inr))
          (Tm.let₁ (Tm.underBinder tf)
            ((Tm.bv 0).case ((Tm.bv 0).inl)
              ((Tm.underBinder (Tm.underBinder (Tm.underBinder tk))).inr)))
          (LambdaIter.coprod B.ty A'.ty) :=
        Eqv.ax (Φ := S.Instr)
          (.sequencing (SequencingAxiom.bindCase (pureEff := S.pureEff)
            (Tm.underBinder tf) ((Tm.bv 0).inl)
            ((Tm.underBinder (Tm.underBinder tk)).inr)))
          hcase hbind
      have s2 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          (Tm.let₁ (Tm.underBinder tf)
            ((Tm.bv 0).case ((Tm.bv 0).inl)
              ((Tm.underBinder (Tm.underBinder (Tm.underBinder tk))).inr)))
          (Tm.let₁ (Tm.underBinder tf)
            ((Tm.bv 0).case ((Tm.bv 0).inl)
              (Tm.let₁ (Tm.underBinder (Tm.underBinder (Tm.underBinder tk)))
                ((Tm.bv 0).inr))))
          (LambdaIter.coprod B.ty A'.ty) :=
        Eqv.let₁ (Eqv.refl hf1)
          (Eqv.case (A := B.ty) (B := A.ty) (Eqv.refl HasType.newest)
            (Eqv.refl (HasType.inl (B := A'.ty) HasType.newest))
            (Syn.eqv_inr_let₁ (A := B.ty) hk3))
      have s4 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          (Tm.let₁ (Tm.underBinder tk)
            (Tm.underBinder (Tm.underBinder tf')))
          (Tm.instantiate (Tm.underBinder (Tm.underBinder tf'))
            (Tm.underBinder tk))
          (LambdaIter.coprod B.ty A'.ty) :=
        Eqv.ax (Φ := S.Instr)
          (.structural (StructuralAxiom.letBeta (pureEff := S.pureEff)
            (b := Tm.underBinder (Tm.underBinder tf')) hpk1))
          hlet hinst
      have hU := Eqv.uniformity (Φ := S.Instr) (B := B.ty)
        (HasType.newest (Φ := S.Instr) (Γ := Ctx.nil)
          (β := BoundCtx.nil) (A := A.ty))
        hk1 hpk1 hf1 hf'1
        (((s1.trans s2).trans (hsq1.trans s4)))
      -- fold the transported iteration back into a composite
      have hidk : Eqv (Φ := S.Instr) S.pureEff Ctx.nil
          (BoundCtx.nil.snoc A.ty)
          (Tm.let₁ (Tm.bv 0) (Tm.underBinder tk)) tk A'.ty :=
        Syn.eqv_of_mk_eq (h := HasType.let₁ HasType.newest hk1) (h' := htk)
          (id'_comp (mk htk))
      have u2 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil
          (BoundCtx.nil.snoc A.ty)
          (Tm.iter (Tm.let₁ (Tm.bv 0) (Tm.underBinder tk))
            (Tm.underBinder tf'))
          (Tm.iter tk (Tm.underBinder tf')) B.ty :=
        Eqv.iter (A := A'.ty) (B := B.ty) hidk (Eqv.refl hf'1)
      have u3 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil
          (BoundCtx.nil.snoc A.ty)
          (Tm.iter tk (Tm.underBinder tf'))
          (Tm.let₁ tk
            (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf'))))
          B.ty :=
        Eqv.ax (Φ := S.Instr)
          (.iteration (IterationAxiom.iterBind (pureEff := S.pureEff)
            tk (Tm.underBinder tf')))
          (HasType.iter (A := A'.ty) (B := B.ty) htk hf'1)
          (HasType.let₁ htk
            (HasType.iter (A := A'.ty) (B := B.ty) HasType.newest hf'2b))
      have key : Eqv (Φ := S.Instr) S.pureEff Ctx.nil
          (BoundCtx.nil.snoc A.ty)
          (Tm.iter (Tm.bv 0) (Tm.underBinder tf))
          (Tm.let₁ tk
            (Tm.underBinder (Tm.iter (Tm.bv 0) (Tm.underBinder tf'))))
          B.ty := by
        rw [Tm.underBinder_iter_underBinder]
        exact hU.trans (u2.trans u3)
      exact Quotient.sound key

/-- Uniformity, phrased with the coproduct action on morphisms — the exact
shape of `CategoryTheory.ElgotFreydCategory.uniformity`, except that the
transported morphism ranges over the pure morphisms of the syntactic category
itself rather than over an ambient value category. -/
theorem iterate_uniformity' {A A' B : SynCat S}
    (f : A ⟶ cop B A) (f' : A' ⟶ cop B A') (k : A ⟶ A') (hk : IsPureMor k)
    (square : f ≫ copMap (𝟙 B) k = k ≫ f') :
    iterate f = k ≫ iterate f' :=
  iterate_uniformity f f' k hk (by rwa [copMap_id_left] at square)

end Syn.SynCat

end Isotope.LambdaIter
