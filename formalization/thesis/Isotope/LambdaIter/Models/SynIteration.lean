import Isotope.LambdaIter.Models.SynCoproduct

/-!
# The Elgot laws for iteration in the syntactic category

`SynCat.iterate` satisfies three of the four equational laws of an Elgot
iteration operator, stated with the coproduct structure of
`Models/SynCoproduct.lean` rather than with raw de Bruijn terms.  The fourth,
uniformity, is in `Models/SynUniformity.lean`.

* **fixpoint**: `iterate f = f ≫ desc (𝟙 B) (iterate f)`, from
  `IterationAxiom.fixpoint`, the identity law, and `bindCase`;
* **naturality**: `iterate f ≫ g = iterate (f ≫ desc (g ≫ injl) injr)`, from
  `IterationAxiom.naturality`, `Syn.eqv_inl_let₁`, and `bindCase`;
* **codiagonal**: `iterate (iterate f) = iterate (f ≫ desc (𝟙 (B + A)) injr)`,
  from `IterationAxiom.codiagonal` and `bindCase`.

These are, term for term, the three fields of
`CategoryTheory.ElgotCategory` — its `coprod.map g (𝟙 X)` is
`desc (g ≫ injl) injr` — with `cop`, `injl`, `injr`, `desc` in place of
Mathlib's chosen binary coproduct.

The renaming bookkeeping is a handful of instances of one fact: two renamings
of a *one-variable* term agree as soon as they agree at index `0`.

One derived equation does real work and is worth naming: `Syn.eqv_inl_let₁`
says `inl a ≈ let₁ a (inl (bv 0))` even for effectful `a`.  The presentation
has no `bind` scheme for `inl`, so this is obtained by running `caseEta`
backwards at the scrutinee `inl a` and then `caseBetaL` forwards.

## Honest boundary

* **`ElgotCategory (SynCat S)` is not registered as an instance**, and the
  obstruction is *not* these three laws.  `CategoryTheory.ElgotCategory`
  requires `HasFiniteCoproducts`, hence an initial object, and the syntactic
  category is not known to have one.  The empty type is the only candidate,
  and `StructuralAxiom.emptyInitial` fires only on a scrutinee of the literal
  form `.abort a`, so it gives no route to `bv 0 ≈ abort (bv 0)` at type
  `empty`, which is what uniqueness of `empty ⟶ C` needs.  This is a reported
  gap, *not* a proof of non-derivability: no model separating the two terms is
  constructed here.  A presentation carrying "`let₁ a b ≈ let₁ a c` whenever
  `a : empty`" instead would remove the obstruction; changing the presentation
  is out of scope.
* **Uniformity** is proved in `Models/SynUniformity.lean`, in the equational
  form the syntactic axiom supplies and with respect to the wide subcategory
  of pure morphisms defined there.  It is *not* stated as
  `ElgotFreydCategory.uniformity`, which quantifies over morphisms of an
  ambient value category `V` and a functor `J`.
* **Strength is not proved**, and cannot even be stated: the syntactic
  category carries no premonoidal or distributive structure here.
* Consequently the syntactic category is **not** shown to be a Freyd,
  distributive Freyd, or (strong) Elgot Freyd category, and issue #57 remains
  open.  What is established is: it is a category, it has binary coproducts,
  its iteration operator is well defined on classes, and that operator
  satisfies all four *equational* Elgot laws.
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

/-- The body of `iterate (f ≫ desc (g ≫ injl) injr)`, in normal form. -/
theorem underBinder_naturality_body (b c : Tm ν Φ 1) :
    Tm.underBinder (Tm.let₁ b
        (Tm.underBinder ((Tm.bv 0).case
          (Tm.underBinder (Tm.let₁ c (Tm.underBinder ((Tm.bv 0).inl))))
          (Tm.underBinder ((Tm.bv 0).inr))))) =
      Tm.let₁ (Tm.underBinder b)
        ((Tm.bv 0).case
          (Tm.let₁ (Tm.underBinder (Tm.underBinder (Tm.underBinder c)))
            ((Tm.bv 0).inl))
          ((Tm.bv 0).inr)) :=
  congrArg (fun x : Tm ν Φ 4 =>
      Tm.let₁ (Tm.underBinder b)
        ((Tm.bv 0).case (Tm.let₁ x ((Tm.bv 0).inl)) ((Tm.bv 0).inr)))
    (rename_upRen_upRen_underBinder _ _ c)

/-- Shifting a one-variable iteration whose body is already shifted. -/
theorem underBinder_iter_underBinder (c : Tm ν Φ 1) :
    Tm.underBinder (Tm.iter (Tm.bv 0) (Tm.underBinder c)) =
      Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder c)) :=
  congrArg (fun x : Tm ν Φ 3 => Tm.iter (Tm.bv 0) x)
    (rename_upRen_underBinder _ c)

end LocallyNameless.Tm

namespace Syn

variable {S : Sig.{u}}

/-- **Injections bind their argument.**  `inl a` and `let₁ a (inl (bv 0))` are
provably equal even when `a` is effectful.  This is derived, not an axiom: run
`caseEta` backwards at the scrutinee `inl a`, then `caseBetaL` forwards.  The
presentation has no `bind` scheme for `inl`, so this detour is what makes the
naturality law below reachable. -/
theorem eqv_inl_let₁ {S : Sig.{u}} {n : Nat} {β : BoundCtx S.Ty n}
    {a : Tm Empty S.Instr n} {A B : S.Ty}
    (ha : HasType S.Instr Ctx.nil β a A) :
    Eqv (Φ := S.Instr) S.pureEff Ctx.nil β
      ((Tm.inl a)) (Tm.let₁ a ((Tm.bv 0).inl))
      (LambdaIter.coprod A B) :=
  have hcase : HasType S.Instr Ctx.nil β
      ((Tm.inl a).case ((Tm.bv 0).inl) ((Tm.bv 0).inr))
      (LambdaIter.coprod A B) :=
    HasType.case (A := A) (B := B) (HasType.inl (B := B) ha)
      (HasType.inl (B := B) HasType.newest)
      (HasType.inr (A := A) HasType.newest)
  Eqv.trans
    (Eqv.symm (Eqv.ax (Φ := S.Instr)
      (.structural (StructuralAxiom.caseEta (pureEff := S.pureEff) (Tm.inl a)))
      hcase (HasType.inl (B := B) ha)))
    (Eqv.ax (Φ := S.Instr)
      (.structural (StructuralAxiom.caseBetaL (pureEff := S.pureEff)
        a ((Tm.bv 0).inl) ((Tm.bv 0).inr)))
      hcase (HasType.let₁ ha (HasType.inl (B := B) HasType.newest)))

/-- The mirror image of `eqv_inl_let₁` for the right injection. -/
theorem eqv_inr_let₁ {S : Sig.{u}} {n : Nat} {β : BoundCtx S.Ty n}
    {b : Tm Empty S.Instr n} {A B : S.Ty}
    (hb : HasType S.Instr Ctx.nil β b B) :
    Eqv (Φ := S.Instr) S.pureEff Ctx.nil β
      ((Tm.inr b)) (Tm.let₁ b ((Tm.bv 0).inr))
      (LambdaIter.coprod A B) :=
  have hcase : HasType S.Instr Ctx.nil β
      ((Tm.inr b).case ((Tm.bv 0).inl) ((Tm.bv 0).inr))
      (LambdaIter.coprod A B) :=
    HasType.case (A := A) (B := B) (HasType.inr (A := A) hb)
      (HasType.inl (B := B) HasType.newest)
      (HasType.inr (A := A) HasType.newest)
  Eqv.trans
    (Eqv.symm (Eqv.ax (Φ := S.Instr)
      (.structural (StructuralAxiom.caseEta (pureEff := S.pureEff) (Tm.inr b)))
      hcase (HasType.inr (A := A) hb)))
    (Eqv.ax (Φ := S.Instr)
      (.structural (StructuralAxiom.caseBetaR (pureEff := S.pureEff)
        b ((Tm.bv 0).inl) ((Tm.bv 0).inr)))
      hcase (HasType.let₁ hb (HasType.inr (A := A) HasType.newest)))

end Syn

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

/-- **The naturality law.**  Postcomposing an iteration is iterating the
postcomposed body.

The derivation is `IterationAxiom.naturality`, then `Syn.eqv_inl_let₁` to turn
the axiom's `inl (…)` into the composite `g ≫ injl`, then
`SequencingAxiom.bindCase`. -/
theorem iterate_naturality {A B C : SynCat S} (f : A ⟶ cop B A) (g : B ⟶ C) :
    iterate f ≫ g = iterate (f ≫ desc (g ≫ injl C A) (injr C A)) := by
  induction f using Syn.ind with
  | H tf hf =>
    induction g using Syn.ind with
    | H tg hg =>
      have h1 := hf.underBinder (X := A.ty)
      have hg2 := (hg.underBinder (X := A.ty)).underBinder (X := A.ty)
      have hg3 := ((hg.underBinder (X := A.ty)).underBinder (X := A.ty)
        ).underBinder (X := LambdaIter.coprod B.ty A.ty)
      have hiter : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
          (Tm.iter (Tm.bv 0) (Tm.underBinder tf)) B.ty :=
        HasType.iter (A := A.ty) (B := B.ty) HasType.newest h1
      have hR : HasType S.Instr Ctx.nil
          (((BoundCtx.nil.snoc A.ty).snoc A.ty).snoc A.ty)
          (((Tm.bv 0).inr : Tm Empty S.Instr 3))
          (LambdaIter.coprod C.ty A.ty) :=
        HasType.inr (A := C.ty) HasType.newest
      have hbody₁ : HasType S.Instr Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          ((Tm.underBinder tf).case
            ((Tm.underBinder (Tm.underBinder tg)).inl) ((Tm.bv 0).inr))
          (LambdaIter.coprod C.ty A.ty) :=
        HasType.case (A := B.ty) (B := A.ty) h1
          (HasType.inl (B := A.ty) hg2) hR
      have hbody₁' : HasType S.Instr Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          ((Tm.underBinder tf).case
            (Tm.let₁ (Tm.underBinder (Tm.underBinder tg)) ((Tm.bv 0).inl))
            ((Tm.bv 0).inr))
          (LambdaIter.coprod C.ty A.ty) :=
        HasType.case (A := B.ty) (B := A.ty) h1
          (HasType.let₁ hg2 (HasType.inl (B := A.ty) HasType.newest)) hR
      have hbody₂ : HasType S.Instr Ctx.nil
          ((BoundCtx.nil.snoc A.ty).snoc A.ty)
          (Tm.let₁ (Tm.underBinder tf)
            ((Tm.bv 0).case
              (Tm.let₁ (Tm.underBinder (Tm.underBinder (Tm.underBinder tg)))
                ((Tm.bv 0).inl))
              ((Tm.bv 0).inr)))
          (LambdaIter.coprod C.ty A.ty) :=
        HasType.let₁ h1
          (HasType.case (A := B.ty) (B := A.ty) HasType.newest
            (HasType.let₁ hg3 (HasType.inl (B := A.ty) HasType.newest))
            (HasType.inr (A := C.ty) HasType.newest))
      have s1 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
          (Tm.let₁ (Tm.iter (Tm.bv 0) (Tm.underBinder tf))
            (Tm.underBinder tg))
          (Tm.iter (Tm.bv 0)
            ((Tm.underBinder tf).case
              ((Tm.underBinder (Tm.underBinder tg)).inl) ((Tm.bv 0).inr)))
          C.ty :=
        Eqv.ax (Φ := S.Instr)
          (.iteration (IterationAxiom.naturality (pureEff := S.pureEff)
            (.bv (0 : Fin 1)) (Tm.underBinder tf) (Tm.underBinder tg)))
          (HasType.let₁ hiter (hg.underBinder (X := A.ty)))
          (HasType.iter (A := A.ty) (B := C.ty) HasType.newest hbody₁)
      have s2 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
          (Tm.iter (Tm.bv 0)
            ((Tm.underBinder tf).case
              ((Tm.underBinder (Tm.underBinder tg)).inl) ((Tm.bv 0).inr)))
          (Tm.iter (Tm.bv 0)
            ((Tm.underBinder tf).case
              (Tm.let₁ (Tm.underBinder (Tm.underBinder tg)) ((Tm.bv 0).inl))
              ((Tm.bv 0).inr)))
          C.ty :=
        Eqv.iter (A := A.ty) (B := C.ty) (Eqv.refl HasType.newest)
          (Eqv.case (A := B.ty) (B := A.ty) (Eqv.refl h1)
            (Syn.eqv_inl_let₁ (B := A.ty) hg2) (Eqv.refl hR))
      have s3 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
          (Tm.iter (Tm.bv 0)
            ((Tm.underBinder tf).case
              (Tm.let₁ (Tm.underBinder (Tm.underBinder tg)) ((Tm.bv 0).inl))
              ((Tm.bv 0).inr)))
          (Tm.iter (Tm.bv 0)
            (Tm.let₁ (Tm.underBinder tf)
              ((Tm.bv 0).case
                (Tm.let₁ (Tm.underBinder (Tm.underBinder (Tm.underBinder tg)))
                  ((Tm.bv 0).inl))
                ((Tm.bv 0).inr))))
          C.ty :=
        Eqv.iter (A := A.ty) (B := C.ty) (Eqv.refl HasType.newest)
          (Eqv.ax (Φ := S.Instr)
            (.sequencing (SequencingAxiom.bindCase (pureEff := S.pureEff)
              (Tm.underBinder tf)
              (Tm.let₁ (Tm.underBinder (Tm.underBinder tg)) ((Tm.bv 0).inl))
              ((Tm.bv 0).inr)))
            hbody₁' hbody₂)
      have key : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
          (Tm.let₁ (Tm.iter (Tm.bv 0) (Tm.underBinder tf))
            (Tm.underBinder tg))
          (Tm.iter (Tm.bv 0)
            (Tm.underBinder (Tm.let₁ tf
              (Tm.underBinder ((Tm.bv 0).case
                (Tm.underBinder
                  (Tm.let₁ tg (Tm.underBinder ((Tm.bv 0).inl))))
                (Tm.underBinder ((Tm.bv 0).inr)))))))
          C.ty := by
        rw [Tm.underBinder_naturality_body]
        exact (s1.trans s2).trans s3
      exact Quotient.sound key

/-- **The codiagonal law.**  Iterating an iteration is iterating once, with
the two "continue" branches merged.

The derivation is `IterationAxiom.codiagonal` followed by
`SequencingAxiom.bindCase`; the only renaming step is that shifting
`iterate f` shifts its body twice. -/
theorem iterate_codiagonal {A B : SynCat S} (f : A ⟶ cop (cop B A) A) :
    iterate (iterate f) = iterate (f ≫ desc (𝟙 (cop B A)) (injr B A)) := by
  induction f using Syn.ind with
  | H tf hf =>
    have h1 := hf.underBinder (X := A.ty)
    have h2 := h1.underBinder (X := A.ty)
    have hR : HasType S.Instr Ctx.nil
        (((BoundCtx.nil.snoc A.ty).snoc A.ty).snoc A.ty)
        (((Tm.bv 0).inr : Tm Empty S.Instr 3))
        (LambdaIter.coprod B.ty A.ty) :=
      HasType.inr (A := B.ty) HasType.newest
    have hlhs : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.iter (Tm.bv 0)
          (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf)))) B.ty :=
      HasType.iter (A := A.ty) (B := B.ty) HasType.newest
        (HasType.iter (A := A.ty) (B := LambdaIter.coprod B.ty A.ty)
          HasType.newest h2)
    have hmid : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.iter (Tm.bv 0)
          ((Tm.underBinder tf).case (Tm.bv 0) ((Tm.bv 0).inr))) B.ty :=
      HasType.iter (A := A.ty) (B := B.ty) HasType.newest
        (HasType.case (A := LambdaIter.coprod B.ty A.ty) (B := A.ty) h1
          HasType.newest hR)
    have hrhs : HasType S.Instr Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.iter (Tm.bv 0)
          (Tm.let₁ (Tm.underBinder tf)
            ((Tm.bv 0).case (Tm.bv 0) ((Tm.bv 0).inr)))) B.ty :=
      HasType.iter (A := A.ty) (B := B.ty) HasType.newest
        (HasType.let₁ h1
          (HasType.case (A := LambdaIter.coprod B.ty A.ty) (B := A.ty)
            HasType.newest HasType.newest
            (HasType.inr (A := B.ty) HasType.newest)))
    have s1 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.iter (Tm.bv 0)
          (Tm.iter (Tm.bv 0) (Tm.underBinder (Tm.underBinder tf))))
        (Tm.iter (Tm.bv 0)
          ((Tm.underBinder tf).case (Tm.bv 0) ((Tm.bv 0).inr))) B.ty :=
      Eqv.ax (Φ := S.Instr)
        (.iteration (IterationAxiom.codiagonal (pureEff := S.pureEff)
          ((Tm.bv 0 : Tm Empty S.Instr 1)) (Tm.underBinder tf)))
        hlhs hmid
    have s2 : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.iter (Tm.bv 0)
          ((Tm.underBinder tf).case (Tm.bv 0) ((Tm.bv 0).inr)))
        (Tm.iter (Tm.bv 0)
          (Tm.let₁ (Tm.underBinder tf)
            ((Tm.bv 0).case (Tm.bv 0) ((Tm.bv 0).inr)))) B.ty :=
      Eqv.iter (A := A.ty) (B := B.ty) (Eqv.refl HasType.newest)
        (Eqv.ax (Φ := S.Instr)
          (.sequencing (SequencingAxiom.bindCase (pureEff := S.pureEff)
            (Tm.underBinder tf) ((Tm.bv 0 : Tm Empty S.Instr 3))
            ((Tm.bv 0).inr)))
          (HasType.case (A := LambdaIter.coprod B.ty A.ty) (B := A.ty) h1
            HasType.newest hR)
          (HasType.let₁ h1
            (HasType.case (A := LambdaIter.coprod B.ty A.ty) (B := A.ty)
              HasType.newest HasType.newest
              (HasType.inr (A := B.ty) HasType.newest))))
    have key : Eqv (Φ := S.Instr) S.pureEff Ctx.nil (BoundCtx.nil.snoc A.ty)
        (Tm.iter (Tm.bv 0)
          (Tm.underBinder (Tm.iter (Tm.bv 0) (Tm.underBinder tf))))
        (Tm.iter (Tm.bv 0)
          (Tm.underBinder (Tm.let₁ tf
            (Tm.underBinder ((Tm.bv 0).case (Tm.underBinder (Tm.bv 0))
              (Tm.underBinder ((Tm.bv 0).inr)))))))
        B.ty := by
      rw [Tm.underBinder_iter_underBinder]
      exact s1.trans s2
    exact Quotient.sound key

/-- Naturality, phrased with the coproduct action on morphisms — the exact
shape of `CategoryTheory.ElgotCategory.naturality`. -/
theorem iterate_naturality' {A B C : SynCat S} (f : A ⟶ cop B A) (g : B ⟶ C) :
    iterate f ≫ g = iterate (f ≫ copMap g (𝟙 A)) := by
  rw [copMap_id_right, iterate_naturality]

end Syn.SynCat

end Isotope.LambdaIter
