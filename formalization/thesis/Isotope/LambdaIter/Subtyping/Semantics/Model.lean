import Isotope.LambdaIter.Subtyping.LocallyNameless.Typing

/-!
# Set-valued models of lambda-iter types and contexts

The interpretation of a subtype derivation is deliberately part of the
model: distinct derivations need not denote the same coercion.
-/

namespace Isotope.LambdaIter.Subtyping.Semantics

universe u v

/-- A set-valued interpretation of a lambda-iter type universe. -/
class TypeModel (τ : Type u) [TypeFormers τ] [Subtyping τ] where
  interp : τ → Type v
  tensorEquiv (A B : τ) : interp (TypeFormers.tensor A B) ≃ interp A × interp B
  unitEquiv : interp (TypeFormers.unit : τ) ≃ Unit
  coprodEquiv (A B : τ) : interp (TypeFormers.coprod A B) ≃ Sum (interp A) (interp B)
  emptyEquiv : interp (TypeFormers.empty : τ) ≃ Empty
  coe {A B : τ} : Subty A B → interp A → interp B

/-- Coherence needed when equational reasoning identifies composite subtype
derivations. This does not collapse arbitrary proof-relevant derivations: only
the operations exposed by `Subtyping` receive their expected semantics. -/
class LawfulTypeModel (τ : Type u) [TypeFormers τ] [Subtyping τ]
    [TypeModel.{u, v} τ] : Prop where
  coe_refl (A : τ) : TypeModel.coe (Subty.refl A) = id
  coe_trans {A B C : τ} (f : Subty A B) (g : Subty B C) :
    TypeModel.coe (Subty.trans f g) = TypeModel.coe g ∘ TypeModel.coe f
  coe_tensor {A A' B B' : τ} (f : Subty A A') (g : Subty B B')
      (p : TypeModel.interp (TypeFormers.tensor A B)) :
    TypeModel.tensorEquiv A' B' (TypeModel.coe (Subty.tensor f g) p) =
      (TypeModel.coe f (TypeModel.tensorEquiv A B p).1,
       TypeModel.coe g (TypeModel.tensorEquiv A B p).2)
  coe_coprod {A A' B B' : τ} (f : Subty A A') (g : Subty B B')
      (s : TypeModel.interp (TypeFormers.coprod A B)) :
    TypeModel.coprodEquiv A' B' (TypeModel.coe (Subty.coprod f g) s) =
      Sum.map (TypeModel.coe f) (TypeModel.coe g) (TypeModel.coprodEquiv A B s)
  coe_empty (A : τ) (z : TypeModel.interp (TypeFormers.empty : τ)) :
    TypeModel.coe (Subty.empty A) z = Empty.elim (TypeModel.emptyEquiv z)
  coe_unit (A : τ) (a : TypeModel.interp A) :
    TypeModel.unitEquiv (TypeModel.coe (Subty.unit A) a) = ()

/-- Optional semantic proof irrelevance for subtype witnesses.  This is
separate from the structural laws because refinement semantics may
intentionally interpret distinct derivations differently. -/
class SubtyProofIrrelevant (τ : Type u) [TypeFormers τ] [Subtyping τ]
    [TypeModel.{u, v} τ] : Prop where
  coe_eq {A B : τ} (f g : Subty A B) : TypeModel.coe f = TypeModel.coe g

/-- Propositionally unique syntax-level witnesses give semantic proof
irrelevance, independently of the chosen interpretation.  This is a
constructor rather than a global instance because Lean cannot infer the
parameters of a higher-rank family of local `Subsingleton` instances. -/
@[reducible] def subtyProofIrrelevantOfSubsingleton {τ : Type u} [TypeFormers τ]
    [Subtyping τ] [TypeModel.{u, v} τ]
    (h : ∀ A B : τ, Subsingleton (Subty A B)) :
    SubtyProofIrrelevant.{u, v} τ where
  coe_eq {A B} f g := by
    letI := h A B
    rw [Subsingleton.elim f g]

/-- Interpretation of an object-language type. -/
abbrev TyDen [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] (A : τ) :=
  TypeModel.interp A

/-- Semantic coercion associated to a proof-relevant subtyping derivation. -/
def coeSub [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
    {A B : τ} (d : Subty A B) : TyDen A → TyDen B := TypeModel.coe d

/-- Environments retain every context slot, including anonymous and shadowed
ones. The newest slot is the right component. -/
def CtxDen [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    Ctx ν τ → Type (max u v)
  | .nil => PUnit
  | .snoc Γ _ A => CtxDen Γ × TyDen A

/-- Environments for a length-indexed bound context. -/
def BoundDen [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    LocallyNameless.BoundCtx τ n → Type (max u v)
  | .nil => PUnit
  | .snoc β A => BoundDen β × TyDen A

namespace BoundDen

/-- Evaluate a newest-first de Bruijn index in a snoc environment. -/
def get [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    {n : Nat} → {β : LocallyNameless.BoundCtx τ n} →
      BoundDen β → (i : Fin n) → TyDen (β.get i)
  | _ + 1, .snoc _ _, ρ, i => Fin.cases ρ.2 (fun j => get ρ.1 j) i

@[simp] theorem get_zero [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
    {β : LocallyNameless.BoundCtx τ n} {A : τ} (ρ : BoundDen (.snoc β A)) :
    get ρ (0 : Fin (n + 1)) = ρ.2 := rfl

@[simp] theorem get_succ [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
    {β : LocallyNameless.BoundCtx τ n} {A : τ} (ρ : BoundDen (.snoc β A))
    (i : Fin n) : get ρ i.succ = get ρ.1 i := rfl

end BoundDen

namespace CtxDen

/-- Project a larger/refined environment along a proof-relevant weakening.
Retained values are coerced using the subtype witness stored by the
derivation; dropped values are forgotten. -/
def wk [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] [DecidableEq ν] :
    {Γ Δ : Ctx ν τ} → Ctx.Wk Γ Δ → CtxDen Γ → CtxDen Δ
  | _, _, .refl _, ρ => ρ
  | _, _, .trans f g, ρ => wk g (wk f ρ)
  | _, _, .keep f _ d, ρ => (wk f ρ.1, coeSub d ρ.2)
  | _, _, .drop_none f, ρ => wk f ρ.1
  | _, _, .drop_visible f _, ρ => wk f ρ.1

/-- Evaluate a visible free name. The equality carried by typing determines
the result type, while recursion follows the same newest-binding lookup used
by the syntax. -/
def lookup [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
    [DecidableEq ν] : {Γ : Ctx ν τ} → CtxDen Γ →
      (x : ν) → {A : τ} → Γ.lookup x = some A → TyDen A
  | .nil, _, _, _, h => by simp [Ctx.lookup] at h
  | .snoc Γ none B, ρ, x, A, h => lookup ρ.1 x h
  | .snoc Γ (some y) B, ρ, x, A, h => by
      by_cases hxy : x = y
      · subst y
        simp [Ctx.lookup] at h
        cases h
        exact ρ.2
      · exact lookup ρ.1 x (by simpa [Ctx.lookup, hxy] using h)

end CtxDen

namespace BoundDen

/-- Pointwise semantic action of bound-context weakening. -/
def wk [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    {n : Nat} → {β' β : LocallyNameless.BoundCtx τ n} →
      LocallyNameless.BoundCtx.Wk β' β → BoundDen β' → BoundDen β
  | 0, .nil, .nil, .nil, _ => PUnit.unit
  | _ + 1, .snoc _ _, .snoc _ _, .snoc w d, ρ =>
      (wk w ρ.1, coeSub d ρ.2)

/-- Bound weakening is pointwise semantic coercion. -/
theorem get_wk [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ] :
    {n : Nat} → {β' β : LocallyNameless.BoundCtx τ n} →
      (w : LocallyNameless.BoundCtx.Wk β' β) → (ρ : BoundDen β') →
      (i : Fin n) →
      BoundDen.get (wk w ρ) i = coeSub (w.at i) (BoundDen.get ρ i)
  | 0, .nil, .nil, .nil, _, i => Fin.elim0 i
  | _ + 1, .snoc _ _, .snoc _ _, .snoc w d, ρ, i => by
      refine Fin.cases rfl (fun j => ?_) i
      exact get_wk w ρ.1 j

end BoundDen

/-- The additional semantic law required of a free weakening. `FreeWk` keeps
lookup transport separate from its structural derivation; in a
proof-relevant model their chosen coercions must therefore be related
explicitly rather than silently identified. -/
structure RespectsFreeWk [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
    [DecidableEq ν] {Γ' Γ : Ctx ν τ}
    (w : LocallyNameless.FreeWk Γ' Γ) : Prop where
  lookup (γ : CtxDen Γ') (x : ν) (A : τ) (h : Γ.lookup x = some A) :
    let r := w.lookup x A h
    CtxDen.lookup (CtxDen.wk w.structural γ) x h =
      coeSub r.subty (CtxDen.lookup γ x r.found)

end Isotope.LambdaIter.Subtyping.Semantics
