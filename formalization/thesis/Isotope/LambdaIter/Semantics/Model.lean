import Isotope.LambdaIter.LocallyNameless.Typing

/-!
# Set-valued models of lambda-iter types and contexts

The interpretation of a subtype derivation is deliberately part of the
model: distinct derivations need not denote the same coercion.
-/

namespace Isotope.LambdaIter.Semantics

universe u v w

/-- A set-valued interpretation of a lambda-iter type universe. -/
class TypeModel (τ : Type u) [TypeFormers τ] [Subtyping τ] where
  interp : τ → Type v
  tensorEquiv (A B : τ) : interp (tensor A B) ≃ interp A × interp B
  unitEquiv : interp (unit : τ) ≃ Unit
  coprodEquiv (A B : τ) : interp (coprod A B) ≃ Sum (interp A) (interp B)
  emptyElim {C : Sort w} : interp (empty : τ) → C
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
      (p : TypeModel.interp (tensor A B)) :
    TypeModel.tensorEquiv A' B' (TypeModel.coe (Subty.tensor f g) p) =
      (TypeModel.coe f (TypeModel.tensorEquiv A B p).1,
       TypeModel.coe g (TypeModel.tensorEquiv A B p).2)
  coe_coprod {A A' B B' : τ} (f : Subty A A') (g : Subty B B')
      (s : TypeModel.interp (coprod A B)) :
    TypeModel.coprodEquiv A' B' (TypeModel.coe (Subty.coprod f g) s) =
      Sum.map (TypeModel.coe f) (TypeModel.coe g) (TypeModel.coprodEquiv A B s)
  coe_empty (A : τ) (z : TypeModel.interp (empty : τ)) :
    TypeModel.coe (Subty.empty A) z = TypeModel.emptyElim z
  coe_unit (A : τ) (a : TypeModel.interp A) :
    TypeModel.unitEquiv (TypeModel.coe (Subty.unit A) a) = ()

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

end BoundDen

end Isotope.LambdaIter.Semantics
