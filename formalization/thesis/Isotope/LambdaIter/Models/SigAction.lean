import Isotope.LambdaIter.Metatheory.MapInstr
import Isotope.LambdaIter.Models.Alg
import Isotope.LambdaIter.LocallyNameless.BoundCtxMap

/-!
# The action of a signature morphism on typing and on the equational theory

`Isotope/LambdaIter/Metatheory/MapInstr.lean` relabels the *instructions* of a
raw term.  A signature morphism also carries a map of types and a map of
effects, and this file supplies the two consequences that reindexing a model
needs:

* `HasType.map`: a typing derivation over `S` becomes one over `T`, at the
  mapped bound context and the mapped result type;
* `Eqv.map`: the whole equational theory transports.

The transports in `HasType.map` sit in exactly the places dictated by the
coherence fields of a signature morphism — lookup, instruction typing, and the
four type formers — which is precisely where `Alg.Ops.reindex` puts its own.
That parallel is what makes `Alg.Ops.reindex_denote` a plain induction.

Free variables are fixed at `ν := Empty` and the free context at `Ctx.nil`, as
everywhere in `Models/`; the `fv` case is therefore impossible.
-/

namespace Isotope.LambdaIter

open LocallyNameless

universe u w

namespace LocallyNameless.HasType

variable {τ : Type u} [TypeFormers τ] {Φ : Type u} [HasTy Φ τ]

/-- Transport a typing derivation along an equality of result types. -/
def castTy {Γ : Ctx Empty τ} {n : Nat} {β : BoundCtx τ n} {t : Tm Empty Φ n}
    {A A' : τ} (e : A = A') (h : HasType Φ Γ β t A) : HasType Φ Γ β t A' := e ▸ h

@[simp] theorem castTy_rfl {Γ : Ctx Empty τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm Empty Φ n} {A : τ} (h : HasType Φ Γ β t A) :
    castTy rfl h = h := rfl

end LocallyNameless.HasType

namespace LocallyNameless

open Isotope.LambdaIter.LocallyNameless.HasType

variable {S T : Sig.{u}}

/-- **Typing transports along a signature morphism.**  The result type is
`g.ty A`, the bound context is `β.map g.ty`, and the term has its instructions
relabelled by `g.instr`. -/
def HasType.map (g : S ⟶ T) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty},
      HasType S.Instr Ctx.nil β t A →
        HasType T.Instr Ctx.nil (β.map g.ty) (Tm.mapInstr g.instr t) (g.ty A)
  | _, _, _, _, .fv h => absurd h (by simp [Ctx.lookup])
  | _, _, _, _, .bv (β := β) (ι := i) =>
      castTy (BoundCtx.map_get g.ty β i) HasType.bv
  | _, _, _, _, .op (f := f) ha =>
      castTy (g.instr_trg f)
        (HasType.op (castTy (g.instr_src f).symm (HasType.map g ha)))
  | _, _, _, _, .let₁ ha hb => HasType.let₁ (HasType.map g ha) (HasType.map g hb)
  | _, _, _, _, .unit => castTy g.ty_unit.symm HasType.unit
  | _, _, _, _, .pair (A := A) (B := B) ha hb =>
      castTy (g.ty_tensor A B).symm
        (HasType.pair (HasType.map g ha) (HasType.map g hb))
  | _, _, _, _, .let₂ (A := A) (B := B) ha hc =>
      HasType.let₂ (castTy (g.ty_tensor A B) (HasType.map g ha))
        (HasType.map g hc)
  | _, _, _, _, .inl (A := A) (B := B) ha =>
      castTy (g.ty_coprod A B).symm (HasType.inl (HasType.map g ha))
  | _, _, _, _, .inr (A := A) (B := B) hb =>
      castTy (g.ty_coprod A B).symm (HasType.inr (HasType.map g hb))
  | _, _, _, _, .case (A := A) (B := B) he hl hr =>
      HasType.case (castTy (g.ty_coprod A B) (HasType.map g he))
        (HasType.map g hl) (HasType.map g hr)
  | _, _, _, _, .abort ha =>
      HasType.abort (castTy g.ty_empty (HasType.map g ha))
  | _, _, _, _, .iter (A := A) (B := B) ha hb =>
      HasType.iter (HasType.map g ha)
        (castTy (g.ty_coprod B A) (HasType.map g hb))

@[simp] theorem HasType.map_bv (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    (i : Fin n) :
    HasType.map g (HasType.bv (Φ := S.Instr) (Γ := Ctx.nil) (β := β) (ι := i))
      = castTy (BoundCtx.map_get g.ty β i) HasType.bv := rfl

@[simp] theorem HasType.map_op (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    {f : S.Instr} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a (instrSrc f)) :
    HasType.map g (HasType.op ha) =
      castTy (g.instr_trg f)
        (HasType.op (castTy (g.instr_src f).symm (HasType.map g ha))) := rfl

@[simp] theorem HasType.map_let₁ (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    {A B : S.Ty} {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b B) :
    HasType.map g (HasType.let₁ ha hb) =
      HasType.let₁ (HasType.map g ha) (HasType.map g hb) := rfl

@[simp] theorem HasType.map_unit (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n} :
    HasType.map g (HasType.unit (Φ := S.Instr) (Γ := Ctx.nil) (β := β)) =
      castTy g.ty_unit.symm HasType.unit := rfl

@[simp] theorem HasType.map_pair (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    {A B : S.Ty} {a b : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a A) (hb : HasType S.Instr Ctx.nil β b B) :
    HasType.map g (HasType.pair ha hb) =
      castTy (g.ty_tensor A B).symm
        (HasType.pair (HasType.map g ha) (HasType.map g hb)) := rfl

@[simp] theorem HasType.map_let₂ (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    {A B C : S.Ty} {a : Tm Empty S.Instr n} {c : Tm Empty S.Instr (n + 2)}
    (ha : HasType S.Instr Ctx.nil β a (tensor A B))
    (hc : HasType S.Instr Ctx.nil ((β.snoc A).snoc B) c C) :
    HasType.map g (HasType.let₂ ha hc) =
      HasType.let₂ (castTy (g.ty_tensor A B) (HasType.map g ha))
        (HasType.map g hc) := rfl

@[simp] theorem HasType.map_inl (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    {A B : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a A) :
    HasType.map g (HasType.inl (B := B) ha) =
      castTy (g.ty_coprod A B).symm (HasType.inl (HasType.map g ha)) := rfl

@[simp] theorem HasType.map_inr (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    {A B : S.Ty} {b : Tm Empty S.Instr n}
    (hb : HasType S.Instr Ctx.nil β b B) :
    HasType.map g (HasType.inr (A := A) hb) =
      castTy (g.ty_coprod A B).symm (HasType.inr (HasType.map g hb)) := rfl

@[simp] theorem HasType.map_case (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    {A B C : S.Ty} {e : Tm Empty S.Instr n} {l r : Tm Empty S.Instr (n + 1)}
    (he : HasType S.Instr Ctx.nil β e (coprod A B))
    (hl : HasType S.Instr Ctx.nil (β.snoc A) l C)
    (hr : HasType S.Instr Ctx.nil (β.snoc B) r C) :
    HasType.map g (HasType.case he hl hr) =
      HasType.case (castTy (g.ty_coprod A B) (HasType.map g he))
        (HasType.map g hl) (HasType.map g hr) := rfl

@[simp] theorem HasType.map_abort (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    {C : S.Ty} {a : Tm Empty S.Instr n}
    (ha : HasType S.Instr Ctx.nil β a empty) :
    HasType.map g (HasType.abort (C := C) ha) =
      HasType.abort (castTy g.ty_empty (HasType.map g ha)) := rfl

@[simp] theorem HasType.map_iter (g : S ⟶ T) {n : Nat} {β : BoundCtx S.Ty n}
    {A B : S.Ty} {a : Tm Empty S.Instr n} {b : Tm Empty S.Instr (n + 1)}
    (ha : HasType S.Instr Ctx.nil β a A)
    (hb : HasType S.Instr Ctx.nil (β.snoc A) b (coprod B A)) :
    HasType.map g (HasType.iter ha hb) =
      HasType.iter (HasType.map g ha)
        (castTy (g.ty_coprod B A) (HasType.map g hb)) := rfl

/-- **The equational theory transports along a signature morphism.**  This is
what promotes reindexing from operations to algebras. -/
theorem Eqv.map (g : S ⟶ T) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {a b : Tm Empty S.Instr n} {A : S.Ty},
      Eqv (Φ := S.Instr) S.pureEff Ctx.nil β a b A →
        Eqv (Φ := T.Instr) T.pureEff Ctx.nil (β.map g.ty)
          (Tm.mapInstr g.instr a) (Tm.mapInstr g.instr b) (g.ty A)
  | _, _, _, _, _, .refl h => Eqv.refl (HasType.map g h)
  | _, _, _, _, _, .symm h => Eqv.symm (Eqv.map g h)
  | _, _, _, _, _, .trans h k => Eqv.trans (Eqv.map g h) (Eqv.map g k)
  | _, _, _, _, _, .op h => by
      have ih := Eqv.map g h
      rw [← g.instr_src] at ih
      rw [Tm.mapInstr_op, Tm.mapInstr_op, ← g.instr_trg]
      exact Eqv.op ih
  | _, _, _, _, _, .let₁ ha hb => Eqv.let₁ (Eqv.map g ha) (Eqv.map g hb)
  | _, _, _, _, _, .unit => by rw [g.ty_unit]; exact Eqv.unit
  | _, _, _, _, _, .pair ha hb => by
      rw [g.ty_tensor]; exact Eqv.pair (Eqv.map g ha) (Eqv.map g hb)
  | _, _, _, _, _, .let₂ he hc => by
      have ihe := Eqv.map g he
      rw [g.ty_tensor] at ihe
      exact Eqv.let₂ ihe (Eqv.map g hc)
  | _, _, _, _, _, .inl h => by rw [g.ty_coprod]; exact Eqv.inl (Eqv.map g h)
  | _, _, _, _, _, .inr h => by rw [g.ty_coprod]; exact Eqv.inr (Eqv.map g h)
  | _, _, _, _, _, .case he hl hr => by
      have ihe := Eqv.map g he
      rw [g.ty_coprod] at ihe
      exact Eqv.case ihe (Eqv.map g hl) (Eqv.map g hr)
  | _, _, _, _, _, .abort h => by
      have ih := Eqv.map g h
      rw [g.ty_empty] at ih
      exact Eqv.abort ih
  | _, _, _, _, _, .iter ha hb => by
      have ihb := Eqv.map g hb
      rw [g.ty_coprod] at ihb
      exact Eqv.iter (Eqv.map g ha) ihb
  | _, _, _, _, _, .ax hax ha hb =>
      Eqv.ax (hax.mapInstr (fun _ hf => g.isPure hf))
        (HasType.map g ha) (HasType.map g hb)
  | _, _, _, _, _, .uniformity ha hh hp hb hb' square => by
      have ihsq := Eqv.map g square
      rw [g.ty_coprod] at ihsq
      simp only [Tm.mapInstr_case, Tm.mapInstr_inl, Tm.mapInstr_inr,
        Tm.mapInstr_bv, Tm.mapInstr_underBinder, Tm.mapInstr_instantiate]
        at ihsq
      refine Eqv.uniformity (HasType.map g ha) (HasType.map g hh)
        (hp.mapInstr (fun _ hf => g.isPure hf)) ?_ ?_ ihsq
      · have := HasType.map g hb
        rwa [g.ty_coprod] at this
      · have := HasType.map g hb'
        rwa [g.ty_coprod] at this

end LocallyNameless

end Isotope.LambdaIter
