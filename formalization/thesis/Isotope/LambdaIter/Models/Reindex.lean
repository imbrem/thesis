import Isotope.LambdaIter.Models.Total

/-!
# Reindexing along a signature morphism

A signature morphism `g : S ⟶ T` acts on models **contravariantly**: a model
of `T` is a family of carriers indexed by `T`-types, and `g` can only be
*pre*composed with such a family, never postcomposed.  So `g` sends models of
`T` to models of `S`, not the other way round.  This is forced, not a
convention: the opposite direction would require a left adjoint to
substitution along `g`, which a bare map of type universes does not have.

## What is proved here

* `Alg.Ops.reindex g Y`, the reindexed operations, with carrier
  `(β, A) ↦ Y.El (β.map g.ty) (g.ty A)`.
* `Alg.Ops.proj g Y : HomOver g (reindex g Y) Y`, the canonical map over `g`;
  its underlying function is the identity.
* `Alg.Ops.reindexEquiv`, the **universal property**: maps `X ⟶ Y` over `g`
  correspond exactly to maps `X ⟶ reindex g Y` over `𝟙 S`.  In fibrational
  language, `proj g Y` is a cartesian lift of `g`.
* `Alg.Ops.reindexMap` together with `reindexMap_id` and `reindexMap_comp`:
  **reindexing is a functor** on maps over the identity.  Its construction and
  its functoriality are derived formally from `reindexEquiv` and the unit,
  counit and associativity laws of `HomOver`; no further index bookkeeping is
  needed.
* `Alg.Total.homEquiv`: a morphism of the total category out of `(S, X)` is a
  signature morphism `g` together with a map `X ⟶ g* Y` over the identity.
  This is the honest content of the phrase "fibred over signatures".

## Honest boundary

Everything here is at the level of `Alg.Ops`, the *operations* of a model.  It
does **not** produce a functor `Alg T ⥤ Alg S` between categories of algebras,
because an `Alg` additionally carries the two propositional fields `coh` and
`sound`, and discharging them for `reindex g Y` requires the functorial action
of a signature morphism on the syntax and on the equational theory —
`Tm.map`, `HasType.map`, `Pure.map`, the four axiom schemes, `Eqv.map`, and
their commutation with `rename`, `bsubst` and `instantiate`.  That action is
not built in this development, and no claim is made that it exists here.

What this means precisely: the *universal property* and the *functoriality* of
reindexing are proved, on the structure that carries them; the compatibility of
reindexing with the equational theory is not.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory

universe u w

namespace Alg

namespace Ops

variable {S T U : Sig.{u}}

/-- Reindexing of the operations of a model along a signature morphism.  A
carrier element at `(β, A)` over `S` is one at `(β.map g.ty, g.ty A)` over
`T`; each operation is the corresponding operation of `Y`, transported along
the coherence equations of `g`.

The transports sit in exactly the places dictated by `g`'s coherence fields:
lookup (`var`), instruction typing (`op`), and the four type formers.  The
binder-introducing clauses need none, because `BoundCtx.map` preserves `snoc`
definitionally. -/
def reindex (g : S ⟶ T) (Y : Ops.{u, w} T) : Ops.{u, w} S where
  El β A := Y.El (β.map g.ty) (g.ty A)
  var {_n β} i := Y.tr rfl (BoundCtx.map_get g.ty β i) (Y.var i)
  op f a :=
    Y.tr rfl (g.instr_trg f)
      (Y.op (g.instr f) (Y.tr rfl (g.instr_src f).symm a))
  let₁ a b := Y.let₁ a b
  unit := Y.tr rfl g.ty_unit.symm Y.unit
  pair {_n _β A B} a b := Y.tr rfl (g.ty_tensor A B).symm (Y.pair a b)
  let₂ {_n _β A B _C} a c := Y.let₂ (Y.tr rfl (g.ty_tensor A B) a) c
  inl {_n _β A B} a := Y.tr rfl (g.ty_coprod A B).symm (Y.inl a)
  inr {_n _β A B} b := Y.tr rfl (g.ty_coprod A B).symm (Y.inr b)
  case {_n _β A B _C} e l r := Y.case (Y.tr rfl (g.ty_coprod A B) e) l r
  abort a := Y.abort (Y.tr rfl g.ty_empty a)
  iter {_n _β A B} a b := Y.iter a (Y.tr rfl (g.ty_coprod B A) b)

@[simp] theorem reindex_El (g : S ⟶ T) (Y : Ops.{u, w} T) {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} :
    (reindex g Y).El β A = Y.El (β.map g.ty) (g.ty A) := rfl

/-- The canonical map of models over `g`, out of the reindexed model.  Its
underlying function is the identity: reindexing is *defined* so that this is
so, and every law is either `rfl` or one transport. -/
def proj (g : S ⟶ T) (Y : Ops.{u, w} T) : HomOver g (reindex g Y) Y where
  map x := x
  map_var := fun {_n β} i => tr_heq Y rfl (BoundCtx.map_get g.ty β i) (Y.var i)
  map_op := fun {_n _β} f a =>
    tr_heq Y rfl (g.instr_trg f)
      (Y.op (g.instr f) (Y.tr rfl (g.instr_src f).symm a))
  map_let₁ := fun _ _ => HEq.rfl
  map_unit := tr_heq Y rfl g.ty_unit.symm Y.unit
  map_pair := fun {_n _β A B} a b =>
    tr_heq Y rfl (g.ty_tensor A B).symm (Y.pair a b)
  map_let₂ := fun _ _ => HEq.rfl
  map_inl := fun {_n _β A B} a => tr_heq Y rfl (g.ty_coprod A B).symm (Y.inl a)
  map_inr := fun {_n _β A B} b => tr_heq Y rfl (g.ty_coprod A B).symm (Y.inr b)
  map_case := fun _ _ _ => HEq.rfl
  map_abort := fun _ => HEq.rfl
  map_iter := fun _ _ => HEq.rfl

@[simp] theorem proj_map (g : S ⟶ T) (Y : Ops.{u, w} T) {n : Nat}
    {β : BoundCtx S.Ty n} {A : S.Ty} (x : (reindex g Y).El β A) :
    (proj g Y).map x = x := rfl

/-- The map of models over `𝟙 S` corresponding to a map over `g`. -/
def toReindex {X : Ops.{u, w} S} {Y : Ops.{u, w} T} (g : S ⟶ T)
    (G : HomOver g X Y) : HomOver (𝟙 S) X (reindex g Y) where
  map {_n β _A} x :=
    Y.tr (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl (G.map x)
  map_var := fun {_n β} i =>
    ((tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
          (G.map (X.var i))).trans
        ((G.map_var i).trans
          (heq_var Y (congrArg (BoundCtx.map g.ty)
            (BoundCtx.map_id β).symm) i))).trans
      (tr_heq Y rfl (BoundCtx.map_get g.ty (BoundCtx.map _root_.id β) i)
        (Y.var i)).symm
  map_op := fun {_n β} f a =>
    ((tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
          (G.map (X.op f a))).trans
        ((G.map_op f a).trans
          (heq_op Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
            (g.instr f)
            ((tr_heq Y rfl (g.instr_src f).symm (G.map a)).trans
              ((tr_heq Y rfl (g.instr_src f).symm
                    (Y.tr (congrArg (BoundCtx.map g.ty)
                      (BoundCtx.map_id β).symm) rfl (G.map a))).trans
                (tr_heq Y (congrArg (BoundCtx.map g.ty)
                  (BoundCtx.map_id β).symm) rfl (G.map a))).symm)))).trans
      (tr_heq Y rfl (g.instr_trg f) _).symm
  map_let₁ := fun {_n β _A _B} a b =>
    (tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
        (G.map (X.let₁ a b))).trans
      ((G.map_let₁ a b).trans
        (heq_let₁ Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
          rfl rfl
          (tr_heq Y (congrArg (BoundCtx.map g.ty)
            (BoundCtx.map_id β).symm) rfl (G.map a)).symm
          (tr_heq Y (congrArg (BoundCtx.map g.ty)
            (BoundCtx.map_id (β.snoc _)).symm) rfl (G.map b)).symm))
  map_unit := fun {_n β} =>
    ((tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
          (G.map X.unit)).trans
        (G.map_unit.trans
          (heq_unit Y (congrArg (BoundCtx.map g.ty)
            (BoundCtx.map_id β).symm)))).trans
      (tr_heq Y rfl g.ty_unit.symm Y.unit).symm
  map_pair := fun {_n β A B} a b =>
    ((tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
          (G.map (X.pair a b))).trans
        ((G.map_pair a b).trans
          (heq_pair Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
            rfl rfl
            (tr_heq Y (congrArg (BoundCtx.map g.ty)
              (BoundCtx.map_id β).symm) rfl (G.map a)).symm
            (tr_heq Y (congrArg (BoundCtx.map g.ty)
              (BoundCtx.map_id β).symm) rfl (G.map b)).symm))).trans
      (tr_heq Y rfl (g.ty_tensor A B).symm _).symm
  map_let₂ := fun {_n β A B _C} a c =>
    (tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
        (G.map (X.let₂ a c))).trans
      ((G.map_let₂ a c).trans
        (heq_let₂ Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
          rfl rfl rfl
          ((tr_heq Y rfl (g.ty_tensor A B) (G.map a)).trans
            ((tr_heq Y rfl (g.ty_tensor A B)
                  (Y.tr (congrArg (BoundCtx.map g.ty)
                    (BoundCtx.map_id β).symm) rfl (G.map a))).trans
              (tr_heq Y (congrArg (BoundCtx.map g.ty)
                (BoundCtx.map_id β).symm) rfl (G.map a))).symm)
          (tr_heq Y (congrArg (BoundCtx.map g.ty)
            (BoundCtx.map_id ((β.snoc A).snoc B)).symm) rfl (G.map c)).symm))
  map_inl := fun {_n β A B} a =>
    ((tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
          (G.map (X.inl a))).trans
        ((G.map_inl a).trans
          (heq_inl Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
            rfl rfl
            (tr_heq Y (congrArg (BoundCtx.map g.ty)
              (BoundCtx.map_id β).symm) rfl (G.map a)).symm))).trans
      (tr_heq Y rfl (g.ty_coprod A B).symm _).symm
  map_inr := fun {_n β A B} b =>
    ((tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
          (G.map (X.inr b))).trans
        ((G.map_inr b).trans
          (heq_inr Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
            rfl rfl
            (tr_heq Y (congrArg (BoundCtx.map g.ty)
              (BoundCtx.map_id β).symm) rfl (G.map b)).symm))).trans
      (tr_heq Y rfl (g.ty_coprod A B).symm _).symm
  map_case := fun {_n β A B _C} e l r =>
    (tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
        (G.map (X.case e l r))).trans
      ((G.map_case e l r).trans
        (heq_case Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
          rfl rfl rfl
          ((tr_heq Y rfl (g.ty_coprod A B) (G.map e)).trans
            ((tr_heq Y rfl (g.ty_coprod A B)
                  (Y.tr (congrArg (BoundCtx.map g.ty)
                    (BoundCtx.map_id β).symm) rfl (G.map e))).trans
              (tr_heq Y (congrArg (BoundCtx.map g.ty)
                (BoundCtx.map_id β).symm) rfl (G.map e))).symm)
          (tr_heq Y (congrArg (BoundCtx.map g.ty)
            (BoundCtx.map_id (β.snoc A)).symm) rfl (G.map l)).symm
          (tr_heq Y (congrArg (BoundCtx.map g.ty)
            (BoundCtx.map_id (β.snoc B)).symm) rfl (G.map r)).symm))
  map_abort := fun {_n β _C} a =>
    (tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
        (G.map (X.abort a))).trans
      ((G.map_abort a).trans
        (heq_abort Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
          rfl
          ((tr_heq Y rfl g.ty_empty (G.map a)).trans
            ((tr_heq Y rfl g.ty_empty
                  (Y.tr (congrArg (BoundCtx.map g.ty)
                    (BoundCtx.map_id β).symm) rfl (G.map a))).trans
              (tr_heq Y (congrArg (BoundCtx.map g.ty)
                (BoundCtx.map_id β).symm) rfl (G.map a))).symm)))
  map_iter := fun {_n β A B} a b =>
    (tr_heq Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
        (G.map (X.iter a b))).trans
      ((G.map_iter a b).trans
        (heq_iter Y (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
          rfl rfl
          (tr_heq Y (congrArg (BoundCtx.map g.ty)
            (BoundCtx.map_id β).symm) rfl (G.map a)).symm
          ((tr_heq Y rfl (g.ty_coprod B A) (G.map b)).trans
            ((tr_heq Y rfl (g.ty_coprod B A)
                  (Y.tr (congrArg (BoundCtx.map g.ty)
                    (BoundCtx.map_id (β.snoc A)).symm) rfl (G.map b))).trans
              (tr_heq Y (congrArg (BoundCtx.map g.ty)
                (BoundCtx.map_id (β.snoc A)).symm) rfl (G.map b))).symm)))

@[simp] theorem toReindex_map {X : Ops.{u, w} S} {Y : Ops.{u, w} T}
    (g : S ⟶ T) (G : HomOver g X Y) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} (x : X.El β A) :
    (toReindex g G).map x =
      Y.tr (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl
        (G.map x) := rfl

/-- **The universal property of reindexing.**  Maps of models `X ⟶ Y` over
`g : S ⟶ T` correspond exactly to maps `X ⟶ g* Y` over `𝟙 S`; equivalently,
`proj g Y` is a cartesian lift of `g`. -/
def reindexEquiv (g : S ⟶ T) (X : Ops.{u, w} S) (Y : Ops.{u, w} T) :
    HomOver (𝟙 S) X (reindex g Y) ≃ HomOver g X Y where
  toFun F := F.comp (proj g Y)
  invFun G := toReindex g G
  left_inv F :=
    HomOver.ext fun {_n β _A} x =>
      tr_tr (X := Y) (BoundCtx.map_comp (_root_.id) g.ty β).symm rfl
        (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm) rfl (F.map x)
  right_inv G :=
    HomOver.ext fun {_n β _A} x =>
      tr_tr (X := Y) (congrArg (BoundCtx.map g.ty) (BoundCtx.map_id β).symm)
        rfl (BoundCtx.map_comp (_root_.id) g.ty β).symm rfl (G.map x)

/-- The action of reindexing on maps of models over the identity: this is the
functor `g* : Alg.Ops T ⥤ Alg.Ops S`.  It is *derived* from the universal
property, so no further transport bookkeeping is needed. -/
def reindexMap (g : S ⟶ T) {Y Y' : Ops.{u, w} T} (F : HomOver (𝟙 T) Y Y') :
    HomOver (𝟙 S) (reindex g Y) (reindex g Y') :=
  (reindexEquiv g (reindex g Y) Y').symm ((proj g Y).comp F)

@[simp] theorem reindexEquiv_apply (g : S ⟶ T) (X : Ops.{u, w} S)
    (Y : Ops.{u, w} T) (F : HomOver (𝟙 S) X (reindex g Y)) :
    reindexEquiv g X Y F = F.comp (proj g Y) := rfl

/-- The defining property of `reindexMap`: it is the unique map over `𝟙 S`
making the square with the two cartesian projections commute. -/
theorem comp_proj_reindexMap (g : S ⟶ T) {Y Y' : Ops.{u, w} T}
    (F : HomOver (𝟙 T) Y Y') :
    (reindexMap g F).comp (proj g Y') = (proj g Y).comp F :=
  (reindexEquiv g (reindex g Y) Y').apply_symm_apply _

/-- Reindexing preserves identities. -/
theorem reindexMap_id (g : S ⟶ T) (Y : Ops.{u, w} T) :
    reindexMap g (HomOver.id Y) = HomOver.id (reindex g Y) :=
  (reindexEquiv g (reindex g Y) Y).injective (by
    change (reindexMap g (HomOver.id Y)).comp (proj g Y) =
      (HomOver.id (reindex g Y)).comp (proj g Y)
    rw [comp_proj_reindexMap, HomOver.comp_id, HomOver.id_comp])

/-- Reindexing preserves composition. -/
theorem reindexMap_comp (g : S ⟶ T) {Y Y' Y'' : Ops.{u, w} T}
    (F : HomOver (𝟙 T) Y Y') (F' : HomOver (𝟙 T) Y' Y'') :
    reindexMap g (F.comp F') = (reindexMap g F).comp (reindexMap g F') :=
  (reindexEquiv g (reindex g Y) Y'').injective
    ((comp_proj_reindexMap g (F.comp F')).trans
      ((HomOver.assoc (proj g Y) F F').symm.trans
        ((congrArg (fun m => HomOver.comp m F')
              (comp_proj_reindexMap g F).symm).trans
          ((HomOver.assoc (reindexMap g F) (proj g Y') F').trans
            ((congrArg (fun m => HomOver.comp (reindexMap g F) m)
                  (comp_proj_reindexMap g F').symm).trans
              (HomOver.assoc (reindexMap g F) (reindexMap g F')
                (proj g Y'')).symm)))))

end Ops

end Alg

/-! ### The total category is fibred over signatures -/

namespace Total

open Alg

/-- **A morphism of the total category is a signature morphism together with a
map into the reindexed model.**  This is the honest content of "the total
category is fibred over `Sig`", and it is the decomposition that reduces
initiality in `Total` to initiality of the signature plus fibrewise
initiality. -/
def homEquiv (P Q : Total.{u, w}) :
    (P ⟶ Q) ≃ Σ g : P.sig ⟶ Q.sig,
      Alg.HomOver (𝟙 P.sig) P.alg.toOps (Alg.Ops.reindex g Q.alg.toOps) where
  toFun F := ⟨F.sig, (Ops.reindexEquiv F.sig _ _).symm F.hom⟩
  invFun x := ⟨x.1, Ops.reindexEquiv x.1 _ _ x.2⟩
  left_inv F := Total.Hom.ext' rfl (heq_of_eq (Equiv.apply_symm_apply _ _))
  right_inv x := by
    obtain ⟨g, F⟩ := x
    exact congrArg (Sigma.mk g) (Equiv.symm_apply_apply _ _)

/-- **Initiality in the total category from fibrewise initiality**, in the form
the fibred structure makes natural: the signature is initial, and the
interpretation into every *reindexed* model is unique over the identity.

This is `Total.isInitialOfFibrewise` transported along the universal property
of reindexing.  Combined with `Sig.uniqueFromEmpty`, it says exactly what a
construction of the quotiented syntax over the empty signature would have to
supply for `(Sig.empty, Syn)` to be the initial object of `Total`. -/
def isInitialOfReindex (P : Total.{u, w})
    (hsig : ∀ T : Sig.{u}, Unique (P.sig ⟶ T))
    (halg : ∀ (Q : Total.{u, w}) (g : P.sig ⟶ Q.sig),
      Unique (Alg.HomOver (𝟙 P.sig) P.alg.toOps
        (Alg.Ops.reindex g Q.alg.toOps))) :
    Limits.IsInitial P :=
  isInitialOfFibrewise P hsig fun Q g =>
    letI := halg Q g
    (Alg.Ops.reindexEquiv g P.alg.toOps Q.alg.toOps).symm.unique

end Total

end Isotope.LambdaIter
