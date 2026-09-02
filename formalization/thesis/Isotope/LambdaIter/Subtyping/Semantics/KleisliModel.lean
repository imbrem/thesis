import Isotope.CategoryTheory.Monad.Effectful
import Isotope.LambdaIter.Subtyping.Semantics.Agreement
import Isotope.LambdaIter.Subtyping.Semantics.TwoPoint

/-!
# A concrete model of lambda-iter

Every strong Elgot monad `m` on `Type u` gives a model of λ-iter: types are interpreted as sets,
computations as Kleisli arrows, and the value category is `Type u` itself.  Its Kleisli category
is a concrete effectful Freyd category (`CategoryTheory.Kleisli.effectfulFreydCategory`) over the
two-point effect system, and `denote_mem_eff_kleisli` is effect soundness for it: an instruction
declared pure denotes a `pure`-valued Kleisli arrow, and the whole term does too.
-/

universe u

namespace Isotope.LambdaIter.Subtyping.Semantics

open CategoryTheory CategoryTheory.Limits
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless

/-! ### The standard set-valued interpretation of the free type universe -/

variable {α : Type u}

/-- Interpret a freely generated simple type as a set, given an interpretation of base types. -/
def tyInterp (base : α → Type u) : Ty α → Type u
  | .base a => base a
  | .tensor A B => tyInterp base A × tyInterp base B
  | .unit => PUnit
  | .coprod A B => tyInterp base A ⊕ tyInterp base B
  | .empty => PEmpty

/-- Interpret a subtyping derivation as a coercion of sets. -/
def tySubtyCoe (base : α → Type u) :
    {A B : Ty α} → Ty.Subty A B → tyInterp base A → tyInterp base B
  | _, _, .refl _ => id
  | _, _, .trans f g => tySubtyCoe base g ∘ tySubtyCoe base f
  | _, _, .tensor f g => fun p => (tySubtyCoe base f p.1, tySubtyCoe base g p.2)
  | _, _, .coprod f g => Sum.map (tySubtyCoe base f) (tySubtyCoe base g)
  | _, _, .empty _ => fun z => z.elim
  | _, _, .unit _ => fun _ => PUnit.unit

/-- The standard set-valued type model of the free type universe. -/
@[reducible] def tyModel (base : α → Type u) : TypeModel.{u, u} (Ty α) where
  interp := tyInterp base
  tensorEquiv _ _ := Equiv.refl _
  unitEquiv := (Equiv.punitEquivPUnit : (PUnit : Type u) ≃ PUnit.{1})
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := (Equiv.equivOfIsEmpty (PEmpty : Type u) Empty)
  coe := tySubtyCoe base

/-! ### Signatures interpreted in a monad -/

variable (m : Type u → Type u) [_root_.Monad m] [LawfulMonad m]

/-- Everything needed to interpret a λ-iter signature in the Kleisli category of `m`: sets for
the base types, a Kleisli arrow for each instruction, and a witness that instructions declared
pure really do denote `pure`-valued arrows. -/
structure KleisliSignature (α : Type u) (Φ : Type u) [HasTy Φ (Ty α)] [HasEff Φ Bool] where
  /-- Interpretation of base types. -/
  base : α → Type u
  /-- Interpretation of instructions. -/
  denote (f : Φ) : tyInterp base (instrSrc f) → m (tyInterp base (instrTrg f))
  /-- An instruction declared pure denotes a value. -/
  denote_pure (f : Φ) (h : instrEff f = (⊥ : Bool)) :
    ∃ g : tyInterp base (instrSrc f) → tyInterp base (instrTrg f),
      denote f = fun x => pure (g x)

namespace KleisliSignature

variable {m} {α : Type u} {Φ : Type u} [HasTy Φ (Ty α)] [HasEff Φ Bool]
  (S : KleisliSignature m α Φ)

/-- The categorical type model determined by a signature. -/
@[reducible] noncomputable def typeModel :
    Categorical.TypeModel (Ty α) (Type u) :=
  letI : TypeModel.{u, u} (Ty α) := tyModel S.base
  Categorical.ofTypeModel

/-- The categorical instruction model determined by a signature. -/
noncomputable instance instructionModel :
    Categorical.InstructionModel
      (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM m)) S.typeModel Φ where
  denote f := Kleisli.Hom.mk (S.denote f)

/-- Instructions denote morphisms of the effect they declare. -/
instance effectfulInstructionModel :
    Categorical.EffectfulInstructionModel Bool
      (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM m))
      (Kleisli.eff (Kleisli.Type.TM m)) S.typeModel Φ where
  denote_mem f := by
    cases h : instrEff (ε := Bool) f
    · obtain ⟨g, hg⟩ := S.denote_pure f h
      refine ⟨_, _, rfl, rfl, g, ?_⟩
      apply Kleisli.hom_ext
      simpa [Kleisli.Adjunction.toKleisli] using hg
    · trivial

end KleisliSignature

/-! ### Effect soundness in the concrete model -/

section Soundness

variable {m} {α : Type u} {Φ : Type u} [HasTy Φ (Ty α)] [HasEff Φ Bool]
  [Isotope.Elgot.Iterate m] [Isotope.Elgot.LawfulElgotMonad m]
  (S : KleisliSignature m α Φ)

/-- **Effect soundness in a concrete model.**  A λ-iter term all of whose instructions are
declared pure, and which does not iterate, denotes a `pure`-valued Kleisli arrow; a term with
arbitrary effects denotes an arbitrary Kleisli arrow. -/
theorem denote_mem_eff_kleisli {ν : Type u} [DecidableEq ν]
    {Γ : Ctx ν (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : Tm ν Φ n} {A : Ty α} {e : Bool}
    (h : HasType Φ Γ β t A) (he : HasEffect (fun b => b = true) e t) :
    Kleisli.eff (Kleisli.Type.TM m) e
      (Categorical.denote (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM m)) S.typeModel h) :=
  Categorical.denote_mem_eff _ _ h he

/-- **Purity in the concrete model is `pure`-valuedness.**  A λ-iter term whose instructions are
all declared pure, and which does not iterate, denotes a Kleisli arrow of the form
`fun x => pure (g x)`: a total, effect-free function on environments. -/
theorem denote_pure_kleisli {ν : Type u} [DecidableEq ν]
    {Γ : Ctx ν (Ty α)} {n : Nat} {β : BoundCtx (Ty α) n}
    {t : Tm ν Φ n} {A : Ty α}
    (h : HasType Φ Γ β t A) (he : HasEffect (fun b => b = true) (⊥ : Bool) t) :
    ∃ g : Categorical.envObj S.typeModel Γ β → S.typeModel.obj A,
      (Categorical.denote
        (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM m)) S.typeModel h).of =
          fun x => (pure (g x) : m (S.typeModel.obj A)) :=
  let ⟨g, hg⟩ := (Kleisli.eff_bot_iff _ _).1 (denote_mem_eff_kleisli S h he)
  ⟨g, congrArg Kleisli.Hom.of hg⟩

end Soundness

end Isotope.LambdaIter.Subtyping.Semantics
