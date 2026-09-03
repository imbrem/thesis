import Isotope.LambdaIter.Semantics.Kleisli.Model
import Isotope.LambdaIter.Subtyping.Semantics.KleisliModel
import Isotope.Elgot.Nondet.Powerset
import Isotope.LambdaIter.Models.Categorical.Initial

/-!
# Concrete categorical models of lambda-iter

The instances of `Categorical.TypingCoherent` and `Categorical.LawfulModel`
proved in `Kleisli/Model.lean` are exhibited at two concrete Elgot monads,
partiality and nondeterminism, over a two-instruction signature on the natural
numbers.  This is what makes them non-vacuous: every class hypothesis they
carry is discharged by an actual model, and the resulting categorical
denotation separates terms.
-/

namespace Isotope.LambdaIter.Semantics.Example

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.Elgot
open CategoryTheory

/-- A two-instruction signature on one base type: one pure, one divergent. -/
inductive Instr : Type where
  /-- The successor, declared pure. -/
  | succ
  /-- A divergent instruction. -/
  | diverge
  deriving DecidableEq

/-- Both instructions go from the base type to the base type. -/
instance : HasTy Instr (Ty Unit) where
  src _ := Ty.base ()
  trg _ := Ty.base ()

/-- `succ` is pure and `diverge` is not. -/
instance : HasEff Instr Bool where
  eff
    | .succ => false
    | .diverge => true

/-- The base type denotes the natural numbers. -/
local instance natTypeModel : TypeModel.{0, 0} (Ty Unit) :=
  tyModel (fun _ => Nat)

/-- The bound context holding a single natural number. -/
abbrev β₁ : BoundCtx (Ty Unit) 1 := .snoc .nil (Ty.base ())

section Part

/-- Interpretation of the signature in the partiality monad. -/
noncomputable local instance partInstructionModel :
    InstructionModel Instr (Ty Unit) Bool Part where
  denote
    | .succ => fun (n : Nat) => (pure (n + 1) : _)
    | .diverge => fun _ => Part.none
  denotePure
    | .succ, _ => fun (n : Nat) => (n + 1 : Nat)
    | .diverge, h => by simp [instrEff, HasEff.eff] at h
  denote_pure
    | .succ, _, _ => rfl
    | .diverge, h, _ => by simp [instrEff, HasEff.eff] at h

/-- **The categorical typing-coherence instance is inhabited concretely.** -/
noncomputable example :
    @LocallyNameless.Categorical.TypingCoherent (Ty Unit) _ _ Empty _ Instr _
      (Type 0) (Kleisli (CategoryTheory.ofTypeMonad Part)) _ _ _ _ _ _ _ _ _ _
      _ _ (kleisliJ Part) _ (Categorical.ofTypeModel (τ := Ty Unit))
      (Categorical.ofInstructionModel (ε := Bool)) :=
  instTypingCoherentKleisli

/-- **The categorical lawful-model instance is inhabited concretely.** -/
noncomputable example :
    @LocallyNameless.Categorical.LawfulModel (Ty Unit) _ _ Empty _ Instr _
      Bool _ (⊥ : Bool) (Type 0) (Kleisli (CategoryTheory.ofTypeMonad Part))
      _ _ _ _ _ _ _ _ _ _ _ _ (kleisliJ Part) _
      (Categorical.ofTypeModel (τ := Ty Unit))
      (Categorical.ofInstructionModel (ε := Bool)) :=
  instLawfulModelKleisli

/-- The newest bound variable. -/
def varDeriv : HasType Instr (Ctx.nil : Ctx Empty (Ty Unit)) β₁
    (.bv 0) (Ty.base ()) := HasType.bv

/-- The divergent instruction applied to the newest bound variable. -/
def divDeriv : HasType Instr (Ctx.nil : Ctx Empty (Ty Unit)) β₁
    (.op Instr.diverge (.bv 0)) (Ty.base ()) := HasType.op HasType.bv

/-- The newest bound variable denotes its value. -/
theorem exactDenote_varDeriv :
    exactDenote (ε := Bool) (m := Part) varDeriv PUnit.unit
        (PUnit.unit, (0 : Nat)) = (pure 0 : Part Nat) :=
  exactDenote_bv (τ := Ty Unit) (ν := Empty) (Φ := Instr) (ε := Bool)
    (m := Part) (Γ := Ctx.nil) (β := β₁) (i := 0) PUnit.unit
    (PUnit.unit, (0 : Nat))

/-- The divergent instruction denotes the undefined partial value. -/
theorem exactDenote_divDeriv :
    exactDenote (ε := Bool) (m := Part) divDeriv PUnit.unit
        (PUnit.unit, (0 : Nat)) = Part.none := by
  refine (exactDenote_op (τ := Ty Unit) (ν := Empty) (Φ := Instr) (ε := Bool)
    (m := Part) (Γ := Ctx.nil) (β := β₁) (f := Instr.diverge) PUnit.unit
    (HasType.bv (ι := 0)) (PUnit.unit, (0 : Nat))).trans ?_
  simp only [InstructionModel.denote, partInstructionModel]
  refine Eq.trans ?_ (rfl : (Part.none : Part (TyDen (instrTrg Instr.diverge)))
    = Part.none)
  apply Part.ext
  intro a
  simp

/-- **The categorical denotation separates terms.**  In the partiality model
`x` and `diverge x` denote different Kleisli morphisms, so the categorical
semantics is not degenerate. -/
theorem denote_var_ne_diverge :
    Categorical.denoteOfType (ε := Bool) (m := Part) varDeriv.toGeneric ≠
      Categorical.denoteOfType (ε := Bool) (m := Part) divDeriv.toGeneric := by
  intro hEq
  have h := denoteOfType_pointwise (ε := Bool) hEq PUnit.unit
    (PUnit.unit, (0 : Nat))
  rw [exactDenote_varDeriv, exactDenote_divDeriv] at h
  have h0 : (0 : Nat) ∈ (pure 0 : Part Nat) := by simp
  rw [h] at h0
  exact h0.fst

section Algebra

/-- The running example, packaged as a lambda-iter signature. -/
@[reducible] def exSig : Sig.{0} where
  Ty := Ty Unit
  formers := inferInstance
  Instr := Instr
  Eff := Bool
  pureEff := false
  hasTy := inferInstance
  hasEff := inferInstance

/-- **A Freyd-categorical algebra of lambda-iter.**  The Kleisli category of
the partiality monad, with the interpretation above, is an object of
`Alg exSig` by `Alg.ofCategorical` -- the first algebra in this development
built from a Freyd/Elgot category rather than from a monad directly. -/
noncomputable def partCategoricalAlg : Alg.{0, 0} exSig := by
  letI := Categorical.ofInstructionModel (τ := Ty Unit) (Φ := Instr)
    (ε := Bool) (m := Part)
  exact Alg.ofCategorical (S := exSig) (kleisliJ Part)
    (Categorical.ofTypeModel (τ := Ty Unit))

/-- **Categorical initiality, concretely.**  There is exactly one morphism of
algebras from the quotiented syntax into the Freyd-categorical model above. -/
noncomputable example : Unique (Syn.{0} exSig ⟶ partCategoricalAlg) :=
  Syn.uniqueHom _

end Algebra

end Part

section Nondet

/-- Interpretation of the signature in the powerset monad: `diverge` denotes
the empty set of results. -/
noncomputable local instance setInstructionModel :
    InstructionModel Instr (Ty Unit) Bool SetM where
  denote
    | .succ => fun (n : Nat) => (pure (n + 1) : _)
    | .diverge => fun _ => (∅ : Set _)
  denotePure
    | .succ, _ => fun (n : Nat) => (n + 1 : Nat)
    | .diverge, h => by simp [instrEff, HasEff.eff] at h
  denote_pure
    | .succ, _, _ => rfl
    | .diverge, h, _ => by simp [instrEff, HasEff.eff] at h

/-- **The categorical instances hold for nondeterminism as well.** -/
noncomputable example :
    @LocallyNameless.Categorical.LawfulModel (Ty Unit) _ _ Empty _ Instr _
      Bool _ (⊥ : Bool) (Type 0) (Kleisli (CategoryTheory.ofTypeMonad SetM))
      _ _ _ _ _ _ _ _ _ _ _ _ (kleisliJ SetM) _
      (Categorical.ofTypeModel (τ := Ty Unit))
      (Categorical.ofInstructionModel (ε := Bool)) :=
  instLawfulModelKleisli

/-- The newest bound variable denotes the singleton of its value. -/
theorem exactDenote_varDeriv_set :
    exactDenote (ε := Bool) (m := SetM) varDeriv PUnit.unit
        (PUnit.unit, (0 : Nat)) = (pure 0 : SetM Nat) :=
  exactDenote_bv (τ := Ty Unit) (ν := Empty) (Φ := Instr) (ε := Bool)
    (m := SetM) (Γ := Ctx.nil) (β := β₁) (i := 0) PUnit.unit
    (PUnit.unit, (0 : Nat))

/-- The divergent instruction denotes the empty set of results. -/
theorem exactDenote_divDeriv_set :
    exactDenote (ε := Bool) (m := SetM) divDeriv PUnit.unit
        (PUnit.unit, (0 : Nat)) = (∅ : Set Nat) := by
  refine (exactDenote_op (τ := Ty Unit) (ν := Empty) (Φ := Instr) (ε := Bool)
    (m := SetM) (Γ := Ctx.nil) (β := β₁) (f := Instr.diverge) PUnit.unit
    (HasType.bv (ι := 0)) (PUnit.unit, (0 : Nat))).trans ?_
  simp only [InstructionModel.denote, setInstructionModel]
  have gen : ∀ s : Set (TyDen (τ := Ty Unit) (instrTrg (τ := Ty Unit)
        Instr.diverge)),
      (⋃ _ ∈ s, (∅ : Set (TyDen (τ := Ty Unit)
        (instrTrg (τ := Ty Unit) Instr.diverge)))) = ∅ := by
    intro s
    simp
  exact gen _

/-- **The categorical denotation separates terms in the powerset model too.** -/
theorem denote_var_ne_diverge_set :
    Categorical.denoteOfType (ε := Bool) (m := SetM) varDeriv.toGeneric ≠
      Categorical.denoteOfType (ε := Bool) (m := SetM) divDeriv.toGeneric := by
  intro hEq
  have h := denoteOfType_pointwise (ε := Bool) hEq PUnit.unit
    (PUnit.unit, (0 : Nat))
  rw [exactDenote_varDeriv_set, exactDenote_divDeriv_set] at h
  have h0 : (0 : Nat) ∈ (pure (0 : Nat) : Set Nat) := rfl
  rw [show (pure (0 : Nat) : Set Nat) = (∅ : Set Nat) from h] at h0
  exact h0

end Nondet


end Isotope.LambdaIter.Semantics.Example
