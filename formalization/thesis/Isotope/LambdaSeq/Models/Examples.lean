import Isotope.LambdaSeq.Models.Limits

/-!
# Models with large carriers, and morphisms that are not identities

The terminal model of `Isotope/LambdaSeq/Models/Limits.lean` has singleton
carriers, so every morphism between models built only from it is an identity.
This file supplies models whose carriers are arbitrary types, which is what
makes the category `Alg S` visibly non-thin: it has objects other than the
terminal one, and pairs of distinct parallel morphisms.

## What `const` is, and what it is not

`Alg.const S v` interprets *every* typing derivation by the single element `v`
of an arbitrary carrier `V`.  It satisfies `coh` and `sound` for the cheapest
possible reason — both sides of every required equation are `v`.  It therefore
has **no semantic content**: it distinguishes no two terms.  Its purpose is to
witness that `Alg S` has objects that are not terminal, and non-identity
endomorphisms.
-/

namespace Isotope.LambdaSeq

open LocallyNameless CategoryTheory

open Isotope.LambdaIter (Sig)

universe u w

namespace Alg

variable {S : Sig.{u}} {V V' : Type w}

/-- Operations interpreting every term by a fixed element of `V`. -/
def constOps (S : Sig.{u}) (v : V) : Ops.{u, w} S where
  El _ _ := V
  var _ := v
  op _ _ := v
  let₁ _ _ := v

/-- Every derivation denotes `v` in the constant operations. -/
theorem denote_constOps (S : Sig.{u}) (v : V) :
    ∀ {n : Nat} {β : BoundCtx S.Ty n} {t : Tm Empty S.Instr n} {A : S.Ty}
      (h : HasType S.Instr LambdaIter.Ctx.nil β t A),
      (constOps S v).denote h = v
  | _, _, _, _, .fv h => absurd h (by simp [LambdaIter.Ctx.lookup])
  | _, _, _, _, .bv => rfl
  | _, _, _, _, .op _ => rfl
  | _, _, _, _, .let₁ _ _ => rfl

/-- The constant model on carrier `V` at the point `v`. -/
def const (S : Sig.{u}) (v : V) : Alg.{u, w} S where
  toOps := constOps S v
  coh h k := by rw [denote_constOps, denote_constOps]
  sound h k _ := by rw [denote_constOps, denote_constOps]

@[simp] theorem const_El (S : Sig.{u}) (v : V) {n : Nat} {β : BoundCtx S.Ty n}
    {A : S.Ty} : (const S v).El β A = V := rfl

/-- Any function sending `v` to `v'` is a morphism of constant models. -/
def constHom (S : Sig.{u}) {v : V} {v' : V'} (g : V → V') (hg : g v = v') :
    const S v ⟶ const S v' where
  map x := g x
  map_var _ := hg
  map_op _ _ := hg
  map_let₁ _ _ := hg

@[simp] theorem constHom_map (S : Sig.{u}) {v : V} {v' : V'} (g : V → V')
    (hg : g v = v') {n : Nat} {β : BoundCtx S.Ty n} {A : S.Ty} (x : V) :
    (constHom S g hg).map (β := β) (A := A) x = g x := rfl

/-! ### The category of models is not thin, and not everything is terminal -/

/-- A `Bool`-carried constant model is not terminal: the unique map into the
terminal model is not injective, because its carrier has two elements. -/
theorem const_not_terminal (S : Sig.{u}) (A : S.Ty) :
    ¬ Function.Injective
      (fun x : Bool => (default : const S true ⟶ terminal.{u, 0} S).map
        (n := 0) (β := LambdaIter.LocallyNameless.BoundCtx.nil) (A := A) x) := by
  intro h
  exact Bool.noConfusion (h (a₁ := true) (a₂ := false) rfl)

/-- The constant map `Bool → Bool` at `true` is an endomorphism of
`const S true` distinct from the identity.  Hence `Alg S` has parallel
morphisms that differ. -/
theorem constHom_ne_id (S : Sig.{u}) (A : S.Ty) :
    constHom S (fun _ : Bool => true) rfl ≠ 𝟙 (const S (true : Bool)) := by
  intro h
  have h' := congrArg
    (fun F : const S (true : Bool) ⟶ const S (true : Bool) =>
      F.map (n := 0) (β := LambdaIter.LocallyNameless.BoundCtx.nil) (A := A)
        false) h
  exact Bool.noConfusion h'

/-- Reindexing a power along `not` is not the identity. -/
theorem powReindex_ne_id (S : Sig.{u}) (A : S.Ty) :
    powReindex (W := Bool) (W' := Bool) not (const S (true : Bool)) ≠
      𝟙 (pow Bool (const S (true : Bool))) := by
  intro h
  have h' := congrArg
    (fun F : pow Bool (const S (true : Bool)) ⟶
        pow Bool (const S (true : Bool)) =>
      F.map (n := 0) (β := LambdaIter.LocallyNameless.BoundCtx.nil) (A := A)
        (fun b => b) false) h
  exact Bool.noConfusion h'

end Alg

end Isotope.LambdaSeq
