import Isotope.LambdaIter.Subtyping.Semantics.KleisliModel
import Isotope.Elgot.Nondet.Powerset
import Isotope.Elgot.ITree
import Isotope.Elgot.Transformer.State

/-!
# Concrete effectful Freyd categories and lambda-iter models

Instantiations of `Isotope.LambdaIter.Subtyping.Semantics.KleisliModel` at monads formalized
elsewhere in the development: partiality, nondeterminism, interaction trees, and state over
partiality.  Each gives a concrete effectful Freyd category and a concrete model of λ-iter in
which the effect-soundness theorem holds.
-/

universe u

namespace Isotope.LambdaIter.Subtyping.Semantics

open CategoryTheory Isotope.Elgot

/-! ### Faithful units

The Kleisli inclusion is faithful — so `⊥` really is a copy of the value category rather than a
quotient of it — exactly when `pure` is injective. -/

instance monoPurePart (X : Type u) :
    Mono ((Kleisli.Type.TM _root_.Part).η.app X) := by
  rw [CategoryTheory.mono_iff_injective]
  intro a b h
  simpa using congrArg (fun p : _root_.Part X => a ∈ p) h

instance monoPureSetM (X : Type u) :
    Mono ((Kleisli.Type.TM SetM).η.app X) := by
  rw [CategoryTheory.mono_iff_injective]
  intro a b h
  have h' : (pure a : Set X) = pure b := h
  have : a ∈ (pure b : Set X) := h' ▸ (rfl : a = a)
  simpa using this

/-! ### Concrete effectful Freyd categories -/

/-- Partiality: the Kleisli category of `Part` is an effectful Freyd category whose pure
morphisms are exactly the total, `pure`-valued arrows. -/
noncomputable example :
    EffectfulFreydCategory Bool (Kleisli.eff (Kleisli.Type.TM _root_.Part.{u})) :=
  inferInstance

/-- Nondeterminism: likewise for the powerset monad. -/
noncomputable example :
    EffectfulFreydCategory Bool (Kleisli.eff (Kleisli.Type.TM SetM.{u})) :=
  inferInstance

/-! ### Strong Elgot Freyd structure on the merged models

These are the categories the λ-iter semantics is interpreted in. -/

noncomputable example :
    StrongElgotFreydCategory
      (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM _root_.Part.{u})) := inferInstance

noncomputable example :
    StrongElgotFreydCategory
      (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM SetM.{u})) := inferInstance

noncomputable example (E : Type u → Type u) :
    StrongElgotFreydCategory
      (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM (ITree.Tree.{u} E))) := inferInstance

noncomputable example (S : Type u) :
    StrongElgotFreydCategory
      (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM (StateT.{u, u} S _root_.Part.{u}))) := inferInstance

/-! ### A worked signature

Base type `ℕ`, one pure instruction and one divergent one, interpreted in `Part`. -/

namespace Example

/-- A two-instruction signature: `succ` is pure, `diverge` is not. -/
inductive Instr : Type where
  | succ
  | diverge
  deriving DecidableEq, Repr

instance : HasTy Instr (Ty Unit) where
  src _ := Ty.base ()
  trg _ := Ty.base ()

instance : HasEff Instr Bool where
  eff
    | .succ => false
    | .diverge => true

/-- Interpret the single base type as `ℕ`, `succ` as the successor, and `diverge` as the
nowhere-defined partial function. -/
noncomputable def sig : KleisliSignature _root_.Part Unit Instr where
  base _ := ULift ℕ
  denote
    | .succ => fun n => pure ⟨n.down + 1⟩
    | .diverge => fun _ => Part.none
  denote_pure
    | .succ, _ => ⟨fun n => ⟨n.down + 1⟩, rfl⟩
    | .diverge, h => by simp [instrEff, HasEff.eff] at h

/-- In this model, a term built only from `succ` (and no loops) denotes a *total* function:
`Part` never returns `none`.  This is `denote_pure_kleisli` at the signature above. -/
example {ν : Type} [DecidableEq ν] {Γ : Ctx ν (Ty Unit)} {n : Nat}
    {β : LocallyNameless.BoundCtx (Ty Unit) n}
    {t : LocallyNameless.Tm ν Instr n} {A : Ty Unit}
    (h : LocallyNameless.HasType Instr Γ β t A)
    (he : LocallyNameless.HasEffect (fun b => b = true) (⊥ : Bool) t) :
    ∃ g : Categorical.envObj sig.typeModel Γ β → sig.typeModel.obj A,
      (Categorical.denote
        (Kleisli.Adjunction.toKleisli (Kleisli.Type.TM _root_.Part))
        sig.typeModel h).of =
          fun x => (pure (g x) : _root_.Part (sig.typeModel.obj A)) :=
  denote_pure_kleisli sig h he

end Example

end Isotope.LambdaIter.Subtyping.Semantics
