import Isotope.LambdaIter.Models.SigAction
import Isotope.LambdaIter.Models.Reindex
import Isotope.LambdaIter.Models.Syntax

/-!
# Reindexing an algebra along a signature morphism

`Models/Reindex.lean` reindexes the *operations* of a model.  With the action
of a signature morphism on typing and on the equational theory in hand
(`Models/SigAction.lean`), that reindexing lifts to algebras: the two
propositional obligations of an `Alg` — coherence in the derivation and
soundness for `Eqv` — both follow from

```
(Ops.reindex g Y).denote h = Y.denote (HasType.map g h)
```

which is `Alg.Ops.reindex_denote`.  Its statement carries no transport: both
sides live in `Y.El (β.map g.ty) (g.ty A)`.  Its proof is a plain induction,
because the transports of `Ops.reindex` and those of `HasType.map` sit in
exactly the same places — the coherence fields of the signature morphism.

This closes the gap recorded in the honest boundary of `Models/Reindex.lean`.

## A note on `rw`

Every step below is an explicit `Eq.trans`/`congrArg` term rather than a
rewrite.  The reason is mechanical: in the goal, the term index of
`Ops.denote` is `Tm.mapInstr g.instr (.op f a)` while the derivation's own
index is `.op (g.instr f) (Tm.mapInstr g.instr a)`.  These are definitionally
equal but not syntactically so, and `rw`'s keyed matching therefore fails,
while `exact` succeeds.
-/

namespace Isotope.LambdaIter

open LocallyNameless CategoryTheory

universe u w

namespace Alg.Ops

variable {S T : Sig.{u}}

/-- Denoting a transported derivation is the transported denotation. -/
theorem denote_castTy (Y : Ops.{u, w} T) {n : Nat} {β : BoundCtx T.Ty n}
    {t : Tm Empty T.Instr n} {A A' : T.Ty} (e : A = A')
    (h : HasType T.Instr Ctx.nil β t A) :
    Y.denote (HasType.castTy e h) = Y.tr rfl e (Y.denote h) := by
  cases e; rfl

section DenoteMap

variable (g : S ⟶ T) (Y : Ops.{u, w} T) {n : Nat} {β : BoundCtx S.Ty n}

theorem denote_map_bv (i : Fin n) :
    Y.denote (HasType.map g
        (HasType.bv (Φ := S.Instr) (Γ := Ctx.nil) (β := β) (ι := i)))
      = Y.tr rfl (BoundCtx.map_get g.ty β i) (Y.var i) :=
  denote_castTy Y (BoundCtx.map_get g.ty β i) HasType.bv

theorem denote_map_op {f : S.Instr} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a (instrSrc f)) :
    Y.denote (HasType.map g (HasType.op ha))
      = Y.tr rfl (g.instr_trg f)
        (Y.op (g.instr f)
          (Y.tr rfl (g.instr_src f).symm (Y.denote (HasType.map g ha)))) :=
  (denote_castTy Y (g.instr_trg f) _).trans
    (congrArg (fun x => Y.tr rfl (g.instr_trg f) (Y.op (g.instr f) x))
      (denote_castTy Y (g.instr_src f).symm (HasType.map g ha)))

theorem denote_map_unit :
    Y.denote (HasType.map g
        (HasType.unit (Φ := S.Instr) (Γ := Ctx.nil) (β := β)))
      = Y.tr rfl g.ty_unit.symm Y.unit :=
  denote_castTy Y g.ty_unit.symm HasType.unit

theorem denote_map_pair {A B : S.Ty} {a b : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil β b B) :
    Y.denote (HasType.map g (HasType.pair ha hb))
      = Y.tr rfl (g.ty_tensor A B).symm
        (Y.pair (Y.denote (HasType.map g ha)) (Y.denote (HasType.map g hb))) :=
  denote_castTy Y (g.ty_tensor A B).symm _

theorem denote_map_let₂ {A B C : S.Ty} {a : Tm Empty S.Instr n}
    {c : Tm Empty S.Instr (n + 2)}
    (ha : HasType S.Instr Ctx.nil β a (tensor A B))
    (hc : HasType S.Instr Ctx.nil ((β.snoc A).snoc B) c C) :
    Y.denote (HasType.map g (HasType.let₂ ha hc))
      = Y.let₂ (Y.tr rfl (g.ty_tensor A B) (Y.denote (HasType.map g ha)))
          (Y.denote (HasType.map g hc)) :=
  congrArg (fun x => Y.let₂ x (Y.denote (HasType.map g hc)))
    (denote_castTy Y (g.ty_tensor A B) (HasType.map g ha))

theorem denote_map_inl {A B : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a A) :
    Y.denote (HasType.map g (HasType.inl (B := B) ha))
      = Y.tr rfl (g.ty_coprod A B).symm
        (Y.inl (B := g.ty B) (Y.denote (HasType.map g ha))) :=
  denote_castTy Y (g.ty_coprod A B).symm _

theorem denote_map_inr {A B : S.Ty} {b : Tm Empty S.Instr n}
    (hb : HasType S.Instr Ctx.nil β b B) :
    Y.denote (HasType.map g (HasType.inr (A := A) hb))
      = Y.tr rfl (g.ty_coprod A B).symm
        (Y.inr (A := g.ty A) (Y.denote (HasType.map g hb))) :=
  denote_castTy Y (g.ty_coprod A B).symm _

theorem denote_map_case {A B C : S.Ty} {e : Tm Empty S.Instr n}
    {l r : Tm Empty S.Instr (n + 1)}
    (he : HasType S.Instr Ctx.nil β e (coprod A B))
    (hl : HasType S.Instr Ctx.nil (β.snoc A) l C)
    (hr : HasType S.Instr Ctx.nil (β.snoc B) r C) :
    Y.denote (HasType.map g (HasType.case he hl hr))
      = Y.case (Y.tr rfl (g.ty_coprod A B) (Y.denote (HasType.map g he)))
          (Y.denote (HasType.map g hl)) (Y.denote (HasType.map g hr)) :=
  congrArg
    (fun x => Y.case x (Y.denote (HasType.map g hl)) (Y.denote (HasType.map g hr)))
    (denote_castTy Y (g.ty_coprod A B) (HasType.map g he))

theorem denote_map_abort {C : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a empty) :
    Y.denote (HasType.map g (HasType.abort (C := C) ha))
      = Y.abort (C := g.ty C) (Y.tr rfl g.ty_empty (Y.denote (HasType.map g ha))) :=
  congrArg (fun x => Y.abort (C := g.ty C) x)
    (denote_castTy Y g.ty_empty (HasType.map g ha))

theorem denote_map_iter {A B : S.Ty} {a : Tm Empty S.Instr n}
    {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b (coprod B A)) :
    Y.denote (HasType.map g (HasType.iter ha hb))
      = Y.iter (Y.denote (HasType.map g ha))
          (Y.tr rfl (g.ty_coprod B A) (Y.denote (HasType.map g hb))) :=
  congrArg (fun x => Y.iter (Y.denote (HasType.map g ha)) x)
    (denote_castTy Y (g.ty_coprod B A) (HasType.map g hb))

end DenoteMap

/-- **Denoting in a reindexed model is denoting the mapped derivation.** -/
theorem reindex_denote (g : S ⟶ T) (Y : Ops.{u, w} T) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr Ctx.nil β t A),
      (reindex g Y).denote h = Y.denote (HasType.map g h)
  | _, _, _, _, .fv h => absurd h (by simp [Ctx.lookup])
  | _, _, _, _, .bv => (denote_map_bv g Y _).symm
  | _, _, _, _, .op (f := f) ha => by
      refine Eq.trans ?_ (denote_map_op g Y ha).symm
      exact congrArg
        (fun x => Y.tr rfl (g.instr_trg f)
          (Y.op (g.instr f) (Y.tr rfl (g.instr_src f).symm x)))
        (reindex_denote g Y ha)
  | _, _, _, _, .let₁ (A := A) (B := B) ha hb =>
      congrArg₂ (fun x y => Y.let₁ (A := g.ty A) (B := g.ty B) x y)
        (reindex_denote g Y ha) (reindex_denote g Y hb)
  | _, _, _, _, .unit => (denote_map_unit g Y).symm
  | _, _, _, _, .pair (A := A) (B := B) ha hb => by
      refine Eq.trans ?_ (denote_map_pair g Y ha hb).symm
      exact congrArg₂
        (fun x y => Y.tr rfl (g.ty_tensor A B).symm
          (Y.pair (A := g.ty A) (B := g.ty B) x y))
        (reindex_denote g Y ha) (reindex_denote g Y hb)
  | _, _, _, _, .let₂ (A := A) (B := B) (C := C) ha hc => by
      refine Eq.trans ?_ (denote_map_let₂ g Y ha hc).symm
      exact congrArg₂
        (fun x y => Y.let₂ (C := g.ty C) (Y.tr rfl (g.ty_tensor A B) x) y)
        (reindex_denote g Y ha) (reindex_denote g Y hc)
  | _, _, _, _, .inl (A := A) (B := B) ha => by
      refine Eq.trans ?_ (denote_map_inl g Y ha).symm
      exact congrArg
        (fun x => Y.tr rfl (g.ty_coprod A B).symm (Y.inl (B := g.ty B) x))
        (reindex_denote g Y ha)
  | _, _, _, _, .inr (A := A) (B := B) hb => by
      refine Eq.trans ?_ (denote_map_inr g Y hb).symm
      exact congrArg
        (fun x => Y.tr rfl (g.ty_coprod A B).symm (Y.inr (A := g.ty A) x))
        (reindex_denote g Y hb)
  | _, _, _, _, .case (A := A) (B := B) (C := C) he hl hr => by
      refine Eq.trans ?_ (denote_map_case g Y he hl hr).symm
      exact (congrArg₂
          (fun x y => Y.case (C := g.ty C) (Y.tr rfl (g.ty_coprod A B) x) y
            ((reindex g Y).denote hr))
          (reindex_denote g Y he) (reindex_denote g Y hl)).trans
        (congrArg
          (fun z => Y.case (C := g.ty C)
            (Y.tr rfl (g.ty_coprod A B) (Y.denote (HasType.map g he)))
            (Y.denote (HasType.map g hl)) z)
          (reindex_denote g Y hr))
  | _, _, _, _, .abort (C := C) ha => by
      refine Eq.trans ?_ (denote_map_abort g Y ha).symm
      exact congrArg
        (fun x => Y.abort (C := g.ty C) (Y.tr rfl g.ty_empty x))
        (reindex_denote g Y ha)
  | _, _, _, _, .iter (A := A) (B := B) ha hb => by
      refine Eq.trans ?_ (denote_map_iter g Y ha hb).symm
      exact congrArg₂
        (fun x y => Y.iter (A := g.ty A) (B := g.ty B) x
          (Y.tr rfl (g.ty_coprod B A) y))
        (reindex_denote g Y ha) (reindex_denote g Y hb)

end Alg.Ops

/-- **Reindexing an algebra along a signature morphism.**  The operations are
`Alg.Ops.reindex`; coherence and soundness come from those of `Y` through
`Alg.Ops.reindex_denote`, `HasType.map` and `Eqv.map`. -/
def Alg.reindex {S T : Sig.{u}} (g : S ⟶ T) (Y : Alg.{u, w} T) : Alg.{u, w} S where
  toOps := Alg.Ops.reindex g Y.toOps
  coh h k := by
    rw [Alg.Ops.reindex_denote, Alg.Ops.reindex_denote]
    exact Y.coh _ _
  sound h k e := by
    rw [Alg.Ops.reindex_denote, Alg.Ops.reindex_denote]
    exact Y.sound _ _ (Eqv.map g e)

@[simp] theorem Alg.reindex_toOps {S T : Sig.{u}} (g : S ⟶ T) (Y : Alg.{u, w} T) :
    (Alg.reindex g Y).toOps = Alg.Ops.reindex g Y.toOps := rfl

end Isotope.LambdaIter
