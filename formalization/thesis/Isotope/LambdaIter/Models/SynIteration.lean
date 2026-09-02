import Isotope.LambdaIter.Models.SynCoproduct

/-!
# The fixpoint law for iteration in the syntactic category

`SynCat.iterate` satisfies the **fixpoint (unfolding) law** of an Elgot
iteration operator:

```
iterate f = f ≫ desc (𝟙 B) (iterate f)      for  f : A ⟶ B + A
```

so `iterate f` really is a fixpoint of the unfolding map, stated with the
coproduct structure of `Models/SynCoproduct.lean` rather than with raw de
Bruijn terms.

The derivation uses three axioms and one identity law:

1. `IterationAxiom.fixpoint` unfolds `iter (bv 0) (b)` into
   `let₁ (bv 0) (case b (bv 0) (iter (bv 0) …))`;
2. the identity law `𝟙 ≫ g = g` removes the leading `let₁ (bv 0) …`
   (which is `letBeta` at `Pure.bv`);
3. `SequencingAxiom.bindCase` turns `case tf …` into `let₁ tf (case (bv 0) …)`,
   which is exactly the composite `f ≫ desc …`.

The renaming bookkeeping is three lemmas, all instances of the same fact: two
renamings of a *one-variable* term agree as soon as they agree at index `0`.

## Honest boundary

This is **one** Elgot law, not the Elgot structure.  Naturality, codiagonal,
uniformity and strength are not proved, and the syntactic category is not
shown to be a Freyd, distributive Freyd, or Elgot Freyd category — there is no
premonoidal or monoidal structure on it in this repository at all.  Issue #57
therefore remains open; what this file adds is that the fixpoint law, the one
law that makes `iterate` deserve its name, does hold.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory

universe u w q

namespace LocallyNameless.Tm

variable {ν : Type w} {Φ : Type q}

/-- A shift of a doubly shifted one-variable term is the triple shift. -/
theorem rename_upRen_underBinder₂ (σ : Fin 2 → Fin 3) (c : Tm ν Φ 1) :
    Tm.rename (Syntax.upRen σ) (Tm.underBinder (Tm.underBinder c)) =
      Tm.underBinder (Tm.underBinder (Tm.underBinder c)) := by
  simp only [Tm.underBinder, Syntax.rename_comp]
  refine rename_eq_of_zero _ _ ?_ c
  rfl

/-- Two successive shifts of a shifted one-variable term give the triple
shift. -/
theorem rename_upRen_upRen_underBinder (ρ : Fin 1 → Fin 2) (σ : Fin 2 → Fin 3)
    (c : Tm ν Φ 1) :
    Tm.rename (Syntax.upRen σ) (Tm.rename (Syntax.upRen ρ) (Tm.underBinder c)) =
      Tm.underBinder (Tm.underBinder (Tm.underBinder c)) := by
  simp only [Tm.underBinder, Syntax.rename_comp]
  refine rename_eq_of_zero _ _ ?_ c
  rfl

/-- The body of `f ≫ desc (𝟙) (iterate f)`, in normal form. -/
theorem underBinder_desc_body (c : Tm ν Φ 1) :
    Tm.underBinder ((Tm.bv 0).case (Tm.underBinder (Tm.bv 0))
        (Tm.underBinder (Tm.iter (Tm.bv 0) (Tm.underBinder c)))) =
      (Tm.bv 0).case (Tm.bv 0)
        (Tm.iter (Tm.bv 0)
          (Tm.underBinder (Tm.underBinder (Tm.underBinder c)))) :=
  congrArg (fun x : Tm ν Φ 4 =>
      (Tm.bv 0).case (Tm.bv 0) (Tm.iter (Tm.bv 0) x))
    (rename_upRen_upRen_underBinder _ _ c)

/-- The body produced by the fixpoint axiom, in normal form. -/
theorem underBinder_fixpoint_body (c : Tm ν Φ 1) :
    Tm.underBinder (c.case (Tm.bv 0)
        (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder c)))) =
      (Tm.underBinder c).case (Tm.bv 0)
        (Tm.iter (Tm.bv 0)
          (Tm.underBinder (Tm.underBinder (Tm.underBinder c)))) :=
  congrArg (fun x : Tm ν Φ 4 =>
      (Tm.underBinder c).case (Tm.bv 0) (Tm.iter (Tm.bv 0) x))
    (rename_upRen_underBinder₂ _ c)

/-- The right branch produced by the `bindCase` axiom, in normal form. -/
theorem underBinder_iter_branch (c : Tm ν Φ 1) :
    Tm.underBinder (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder c))) =
      Tm.iter (Tm.bv 0)
        (Tm.underBinder (Tm.underBinder (Tm.underBinder c))) :=
  congrArg (fun x : Tm ν Φ 4 => Tm.iter (Tm.bv 0) x)
    (rename_upRen_underBinder₂ _ c)

end LocallyNameless.Tm

namespace Syn.SynCat

variable {S : Sig.{u}}

/-- **The fixpoint law.**  `iterate f` unfolds to `f` followed by the
copairing of the identity with `iterate f` itself.

This is the one Elgot law established for the syntactic category; naturality,
codiagonal, uniformity and strength are not, and no premonoidal or
distributive structure is built (see the module docstring). -/
theorem iterate_fixpoint {A B : SynCat S} (f : A ⟶ cop B A) :
    iterate f = f ≫ desc (𝟙 B) (iterate f) := by
  induction f using Syn.ind with
  | H tf hf =>
    -- The three shifted copies of `tf` that occur.
    have h1 : HasType S.Instr Ctx.nil
        ((BoundCtx.nil.snoc A.ty).snoc A.ty) (Tm.underBinder tf)
        (LambdaIter.coprod B.ty A.ty) := hf.underBinder
    have h2 := h1.underBinder (X := A.ty)
    have h2' := h1.underBinder (X := LambdaIter.coprod B.ty A.ty)
    have h3' := h2'.underBinder (X := A.ty)
    -- `Y`, the body after the fixpoint step and the identity law.
    have hY : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
        (tf.case (Tm.bv 0)
          (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf)))) B.ty :=
      HasType.case (A := B.ty) (B := A.ty) hf HasType.newest
        (HasType.iter (A := A.ty) (B := B.ty) HasType.newest h2)
    have hiter : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.iter (Tm.bv 0) (Tm.underBinder tf)) B.ty :=
      HasType.iter (A := A.ty) (B := B.ty) HasType.newest h1
    have hunfold : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.let₁ (Tm.bv 0)
          (Tm.underBinder (tf.case (Tm.bv 0)
            (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf))))))
        B.ty :=
      HasType.let₁ HasType.newest (hY.underBinder (X := A.ty))
    -- The normal form of the right-hand side's body.
    have hN : HasType S.Instr Ctx.nil
        ((BoundCtx.nil.snoc A.ty).snoc (LambdaIter.coprod B.ty A.ty))
        ((Tm.bv 0).case (Tm.bv 0)
          (Tm.iter (Tm.bv 0)
            (Tm.underBinder (Tm.underBinder (Tm.underBinder tf))))) B.ty :=
      HasType.case (A := B.ty) (B := A.ty) HasType.newest HasType.newest
        (HasType.iter (A := A.ty) (B := B.ty) HasType.newest h3')
    have hrhs : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.let₁ tf
          ((Tm.bv 0).case (Tm.bv 0)
            (Tm.iter (Tm.bv 0)
              (Tm.underBinder (Tm.underBinder (Tm.underBinder tf))))))
        B.ty := HasType.let₁ hf hN
    -- Step 1: unfold by the fixpoint axiom.
    have step1 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.iter (Tm.bv 0) (Tm.underBinder tf))
        (Tm.let₁ (Tm.bv 0)
          (Tm.underBinder (tf.case (Tm.bv 0)
            (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf))))))
        B.ty := by
      refine Eqv.ax (Φ := S.Instr) (.iteration ?_) hiter hunfold
      rw [Tm.underBinder_fixpoint_body]
      exact IterationAxiom.fixpoint (pureEff := S.pureEff)
        (.bv (0 : Fin 1)) (Tm.underBinder tf)
    -- Step 2: discard the leading `let` of the bound variable.
    have step2 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.let₁ (Tm.bv 0)
          (Tm.underBinder (tf.case (Tm.bv 0)
            (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf))))))
        (tf.case (Tm.bv 0)
          (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf)))) B.ty :=
      Syn.eqv_of_mk_eq (h := hunfold) (h' := hY) (id'_comp (mk hY))
    -- Step 3: commute the scrutinee out by `bindCase`.
    have step3 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
        (tf.case (Tm.bv 0)
          (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf))))
        (Tm.let₁ tf
          ((Tm.bv 0).case (Tm.bv 0)
            (Tm.iter (Tm.bv 0)
              (Tm.underBinder (Tm.underBinder (Tm.underBinder tf))))))
        B.ty := by
      refine Eqv.ax (Φ := S.Instr) (.sequencing ?_) hY hrhs
      rw [← Tm.underBinder_iter_branch]
      exact SequencingAxiom.bindCase (pureEff := S.pureEff) tf (Tm.bv 0)
        (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf)))
    have key : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.iter (Tm.bv 0) (Tm.underBinder tf))
        (Tm.let₁ tf
          (Tm.underBinder ((Tm.bv 0).case (Tm.underBinder (Tm.bv 0))
            (Tm.underBinder (Tm.iter (Tm.bv 0) (Tm.underBinder tf))))))
        B.ty := by
      rw [Tm.underBinder_desc_body]
      exact (step1.trans step2).trans step3
    exact Quotient.sound key

end Syn.SynCat

end Isotope.LambdaIter
