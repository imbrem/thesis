import Isotope.LambdaIter.Models.Monadic.Alg
import Isotope.Elgot.Nondet.Finite
import Isotope.Elgot.Nondet.Countable

/-!
# Nondeterminism as a model: the ray signature

This file supplies the signature, the syntax and the semantic computations
that separate *finite* from *countable* nondeterminism as models of the three
calculi.  The three-way summary itself is
`Isotope/LambdaSeq/Models/Monadic/Nondet.lean`; what is proved here is the
lambda-iter half, both the positive (countable) and the negative (finite) one.

## The signature

`raySig` has one base type `N`, one instruction `step : N → N ⊕ N`, and a
two-element effect set in which `step` is *impure*.  A model of it in a monad
`m` is therefore nothing but a Kleisli arrow
`ULift ℕ → m (ULift ℕ ⊕ ULift ℕ)`, and `rayModel` packages exactly that.
The intended arrow is the two-way branching ray

    n ↦ {inl n, inr (n + 1)}

of `Isotope.Elgot.Nondet`: from state `n`, either return `n` or continue from
`n + 1`.  It branches twice, so it is a perfectly good *finite* nondeterministic
computation; but its reachability set from `0` is all of `ℕ`.

## What is proved

* `Alg.ofModel csetRayModel` — countable nondeterminism, with this very body,
  *is* an algebra of lambda-iter, since `CSet` is a lawful Elgot monad.
* `finSet_not_alg_lambdaIter` — for **no** iteration operator whatsoever on the
  finite-powerset monad do the standard operations `ops finRayModel` form an
  algebra of lambda-iter.  The route is the one the equational theory itself
  dictates: soundness for the single axiom `IterationAxiom.fixpoint`, at the
  single closed-up term `iter x (step x)`, already forces the interpretation of
  `iter` to satisfy the Elgot fixpoint law at the ray body, which
  `FinSet.no_fixpoint` refutes.
* `csetLoop_infinite` — the same loop's countable denotation is genuinely
  infinite, which is the concrete reason the finite model cannot exist.

Note what the negative statement quantifies over: an iteration operator `I` on
`FinSet` and an algebra `X` whose operations are *the standard ones*, namely
`ops finRayModel` built from `I`.  It is **not** `¬ Nonempty (Alg raySig)` —
that is false, since a terminal algebra always exists — nor
`¬ Nonempty (Iterate FinSet)`, which is false as well
(`FinSet.nonempty_iterate`).  The impossibility is necessarily relative to
both the laws and the intended interpretation.
-/

namespace Isotope.LambdaIter.Monadic

open Isotope.Elgot
open Isotope.Elgot.Nondet
open LocallyNameless

/-! ### The ray signature -/

/-- The single base type of the ray signature, interpreted by the naturals. -/
inductive RayBase : Type
  /-- The base type of states. -/
  | nat
  deriving DecidableEq, Repr

/-- The single instruction of the ray signature: a step of the ray. -/
inductive RayInstr : Type
  /-- From a state, either stop with it or continue with its successor. -/
  | step
  deriving DecidableEq, Repr

/-- `step` takes a state and returns either a result or a new state. -/
instance instHasTyRay : HasTy RayInstr (Ty RayBase) where
  src _ := .base .nat
  trg _ := .coprod (.base .nat) (.base .nat)

/-- `step` is impure: its effect is `false`, and the pure effect is `true`. -/
instance instHasEffRay : HasEff RayInstr Bool where
  eff _ := false

/-- The ray signature: one base type, one impure instruction branching a state
into a result or a successor state. -/
def raySig : Sig.{0} where
  Ty := Ty RayBase
  formers := inferInstance
  Instr := RayInstr
  Eff := Bool
  pureEff := true
  hasTy := inferInstance
  hasEff := inferInstance

/-- The ray signature's type universe is freely generated, so its formers are
injective and disjoint — the hypothesis the coherence half of the bridge
needs. -/
instance : InjectiveFormers raySig.Ty :=
  inferInstanceAs (InjectiveFormers (Ty RayBase))

/-- The ray signature's only instruction is impure. -/
theorem rayInstr_not_pure : ∀ f : raySig.Instr, ¬ IsPure raySig.pureEff f
  | .step, h => Bool.noConfusion h

/-- The evident interpretation of the ray signature's types: the base type is
`ULift ℕ`, and the four formers are the evident sets. -/
def rayInterp : Ty RayBase → Type
  | .base _ => ULift.{0} ℕ
  | .tensor A B => rayInterp A × rayInterp B
  | .unit => Unit
  | .coprod A B => rayInterp A ⊕ rayInterp B
  | .empty => Empty

/-- A model of the ray signature in a monad `m` is exactly a Kleisli arrow
`ULift ℕ → m (ULift ℕ ⊕ ULift ℕ)`: the interpretation of types is fixed, and
the only instruction is impure, so no purity obligation arises. -/
def rayModel (m : Type → Type) [Monad m]
    (step : ULift.{0} ℕ → m (ULift.{0} ℕ ⊕ ULift.{0} ℕ)) :
    Model.{0, 0} raySig m where
  interp := rayInterp
  denoteInstr := fun | .step => step
  denotePureInstr f hf := absurd hf (rayInstr_not_pure f)
  denoteInstr_pure f hf := absurd hf (rayInstr_not_pure f)
  tensorEquiv _ _ := Equiv.refl _
  unitEquiv := Equiv.refl _
  coprodEquiv _ _ := Equiv.refl _
  emptyEquiv := Equiv.refl _

@[simp] theorem rayModel_interp (m : Type → Type) [Monad m]
    (step : ULift.{0} ℕ → m (ULift.{0} ℕ ⊕ ULift.{0} ℕ)) :
    (rayModel m step).interp = rayInterp := rfl

/-! ### The looping term and the fixpoint axiom instance -/

/-- The base type of states. -/
abbrev N : raySig.Ty := .base .nat

/-- The empty free context of the ray signature. -/
abbrev Γ₀ : Ctx Empty raySig.Ty := .nil

/-- One state in scope. -/
abbrev β₁ : BoundCtx raySig.Ty 1 := .snoc .nil N

/-- Two states in scope. -/
abbrev β₂ : BoundCtx raySig.Ty 2 := .snoc β₁ N

/-- Three states in scope. -/
abbrev β₃ : BoundCtx raySig.Ty 3 := .snoc β₂ N

/-- Four states in scope. -/
abbrev β₄ : BoundCtx raySig.Ty 4 := .snoc β₃ N

/-- The loop body: apply `step` to the current state. -/
abbrev stepBody : Tm Empty raySig.Instr 2 := .op .step (.bv 0)

/-- The ray loop `iter x (step x)`, in one free state variable. -/
abbrev loopTm : Tm Empty raySig.Instr 1 := .iter (.bv 0) stepBody

/-- The right-hand side of the fixpoint axiom at `loopTm`: one unrolling. -/
abbrev rhsTm : Tm Empty raySig.Instr 1 :=
  .let₁ (.bv 0) (.case stepBody (.bv 0)
    (.iter (.bv 0) (Tm.underBinder (Tm.underBinder stepBody))))

/-- The state variable, in one-state scope. -/
def hbv₁ : HasType raySig.Instr Γ₀ β₁ (.bv 0) N := .bv

/-- The state variable, in three-state scope. -/
def hbv₃ : HasType raySig.Instr Γ₀ β₃ (.bv 0) N := .bv

/-- The loop body is typed at `N ⊕ N`. -/
def hstep : HasType raySig.Instr Γ₀ β₂ stepBody (coprod N N) := .op .bv

/-- The loop body, transported under two extra binders. -/
def hstep₄ : HasType raySig.Instr Γ₀ β₄
    (Tm.underBinder (Tm.underBinder stepBody)) (coprod N N) := .op .bv

/-- The ray loop is typed at `N`. -/
def hloop : HasType raySig.Instr Γ₀ β₁ loopTm N := .iter hbv₁ hstep

/-- The loop restarted inside the unrolling. -/
def hinner : HasType raySig.Instr Γ₀ β₃
    (.iter (.bv 0) (Tm.underBinder (Tm.underBinder stepBody))) N :=
  .iter hbv₃ hstep₄

/-- The case analysis inside the unrolling. -/
def hcase : HasType raySig.Instr Γ₀ β₂
    (.case stepBody (.bv 0)
      (.iter (.bv 0) (Tm.underBinder (Tm.underBinder stepBody)))) N :=
  .case hstep hbv₃ hinner

/-- The unrolled loop is typed at `N`. -/
def hrhs : HasType raySig.Instr Γ₀ β₁ rhsTm N := .let₁ hbv₁ hcase

/-- **The fixpoint axiom, instantiated at the ray loop.**  This single
equation is all of lambda-iter's equational theory that the negative result
uses. -/
theorem eqv_fix : Eqv (Φ := raySig.Instr) raySig.pureEff Γ₀ β₁ loopTm rhsTm N :=
  .ax (.iteration (.fixpoint (.bv 0) stepBody)) hloop hrhs

/-! ### Computing the two denotations

Generic in the monad and the step arrow: only the monad laws are used, never
an Elgot law, so these compute equally well in a monad that has no lawful
iteration at all.
-/

section Denote

variable {m : Type → Type} [Monad m] [LawfulMonad m] [Iterate m]
  (step : ULift.{0} ℕ → m (ULift.{0} ℕ ⊕ ULift.{0} ℕ))

/-- The loop body denotes the step arrow. -/
theorem denote_hstep (ρ : (rayModel m step).Env β₂) :
    denote (rayModel m step) hstep ρ = step ρ.2 := by
  change ((pure ρ.2 : m (ULift.{0} ℕ)) >>= step) = _
  rw [pure_bind]

/-- The loop body denotes the step arrow, under two extra binders. -/
theorem denote_hstep₄ (ρ : (rayModel m step).Env β₄) :
    denote (rayModel m step) hstep₄ ρ = step ρ.2 := by
  change ((pure ρ.2 : m (ULift.{0} ℕ)) >>= step) = _
  rw [pure_bind]

omit [Iterate m] in
private theorem ray_body_eq : (fun a : ULift.{0} ℕ =>
    ((pure a : m (ULift.{0} ℕ)) >>= step) >>= (fun s => pure s)) = step := by
  funext a; rw [pure_bind, bind_pure]

/-- **The ray loop denotes the iteration of the step arrow.** -/
theorem denote_hloop (ρ : (rayModel m step).Env β₁) :
    denote (rayModel m step) hloop ρ = Elgot.iter step ρ.2 := by
  change (pure ρ.2 : m (ULift.{0} ℕ)) >>= Elgot.iter (fun a =>
      ((pure a : m (ULift.{0} ℕ)) >>= step) >>= (fun s => pure s)) = _
  rw [pure_bind, ray_body_eq]

/-- The restarted loop denotes the same iteration. -/
theorem denote_hinner (ρ : (rayModel m step).Env β₃) :
    denote (rayModel m step) hinner ρ = Elgot.iter step ρ.2 := by
  change (pure ρ.2 : m (ULift.{0} ℕ)) >>= Elgot.iter (fun a =>
      ((pure a : m (ULift.{0} ℕ)) >>= step) >>= (fun s => pure s)) = _
  rw [pure_bind, ray_body_eq]

/-- The case analysis denotes one unrolling. -/
theorem denote_hcase (ρ : (rayModel m step).Env β₂) :
    denote (rayModel m step) hcase ρ
      = step ρ.2 >>= Sum.elim pure (Elgot.iter step) := by
  simp only [hcase, denote_case, denote_hstep]
  apply bind_congr
  intro e
  cases e with
  | inl a => rfl
  | inr b => exact denote_hinner step (ρ, b)

/-- **The unrolled loop denotes one unrolling of the iteration.** -/
theorem denote_hrhs (ρ : (rayModel m step).Env β₁) :
    denote (rayModel m step) hrhs ρ
      = step ρ.2 >>= Sum.elim pure (Elgot.iter step) := by
  simp only [hrhs, denote_let₁, denote_hcase]
  change (pure ρ.2 : m (ULift.{0} ℕ)) >>= (fun v =>
    step v >>= Sum.elim pure (Elgot.iter step)) = _
  rw [pure_bind]

/-- **Soundness for the single fixpoint axiom forces the Elgot fixpoint law**
at the step arrow.  This is the whole of the negative argument: no property of
the monad beyond lawfulness is used, and no Elgot law is assumed. -/
theorem iterate_fixpoint_of_denote_eq
    (hs : denote (rayModel m step) hloop = denote (rayModel m step) hrhs)
    (n : ULift.{0} ℕ) :
    Elgot.iter step n = step n >>= Sum.elim pure (Elgot.iter step) := by
  have h := congrFun hs (PUnit.unit, n)
  rw [denote_hloop, denote_hrhs] at h
  exact h

end Denote

/-! ### Finite nondeterminism is not a model of lambda-iter -/

/-- The finite-powerset interpretation of the ray signature, with the
two-way branching body of `Isotope.Elgot.Nondet.FinSet.body`.  This is a
perfectly good `Model`: `FinSet` is a lawful monad and the body is finite. -/
abbrev finRayModel : Model.{0, 0} raySig FinSet.{0} :=
  rayModel FinSet.{0} FinSet.body

section FinSet

variable [Iterate FinSet.{0}]

/-- **The standard finite-nondeterminism interpretation is unsound for
lambda-iter**, whatever iteration operator is chosen.

The quantification is over all typing derivations and all `Eqv`-derivable
equations; the witness is the single equation `eqv_fix`. -/
theorem finRay_not_sound :
    ¬ ∀ {n : Nat} {β : BoundCtx raySig.Ty n} {a b : Tm Empty raySig.Instr n}
        {A : raySig.Ty}
        (h : HasType raySig.Instr Γ₀ β a A)
        (k : HasType raySig.Instr Γ₀ β b A),
        Eqv (Φ := raySig.Instr) raySig.pureEff Γ₀ β a b A →
          denote finRayModel h = denote finRayModel k := fun hs =>
  FinSet.no_fixpoint _
    (iterate_fixpoint_of_denote_eq FinSet.body (hs hloop hrhs eqv_fix))

/-- **The standard finite-nondeterminism operations are not an algebra of
lambda-iter**, for the fixed iteration operator of this section. -/
theorem not_alg_finRayModel :
    ¬ ∃ X : Alg.{0, 0} raySig, X.toOps = ops finRayModel := by
  rintro ⟨X, hX⟩
  refine finRay_not_sound (fun h k he => ?_)
  have hd := X.sound h k he
  rw [hX, ops_denote, ops_denote] at hd
  exact hd

end FinSet

/-- **Finite nondeterminism is not a model of lambda-iter.**

Precisely: there is no pair of an iteration operator `I` on the finite-powerset
monad and an algebra `X` of the lambda-iter presentation whose operations are
the standard ones — the Kleisli clauses `ops finRayModel` of the denotation,
with `iter` interpreted by `I`.

This is a law-level statement, and it has to be.  `¬ Nonempty (Alg raySig)` is
false (there is a terminal algebra), and `¬ Nonempty (Iterate FinSet)` is false
as well (`FinSet.nonempty_iterate`: the class carries no equations).  What is
impossible is that the *intended* finite-nondeterministic interpretation be
sound for the lambda-iter equational theory. -/
theorem finSet_not_alg_lambdaIter :
    ¬ ∃ (I : Iterate FinSet.{0}) (X : Alg.{0, 0} raySig),
        X.toOps = @ops raySig FinSet.{0} _ I finRayModel := by
  rintro ⟨I, X, hX⟩
  exact @not_alg_finRayModel I ⟨X, hX⟩

/-! ### Countable nondeterminism is a model of lambda-iter -/

/-- The same two-way branching ray, as a *countable* nondeterministic
computation. -/
def csetBody (n : ULift.{0} ℕ) : CSet.{0} (ULift.{0} ℕ ⊕ ULift.{0} ℕ) :=
  ⟨{Sum.inl n, Sum.inr (ULift.up (n.down + 1))},
    (Set.countable_singleton _).insert _⟩

@[simp] theorem mem_csetBody {n : ULift.{0} ℕ} {s : ULift.{0} ℕ ⊕ ULift.{0} ℕ} :
    s ∈ csetBody n ↔ s = Sum.inl n ∨ s = Sum.inr (ULift.up (n.down + 1)) :=
  Iff.rfl

/-- The countable-powerset interpretation of the ray signature, with the very
same body that defeats the finite one. -/
abbrev csetRayModel : Model.{0, 0} raySig CSet.{0} := rayModel CSet.{0} csetBody

/-- **Countable nondeterminism is a model of lambda-iter.**  `CSet` is a
lawful Elgot monad, so the bridge applies verbatim, with the same signature,
the same interpretation of types and the same interpretation of `step` that
finite nondeterminism cannot support. -/
def csetIterAlg : Alg.{0, 0} raySig := Alg.ofModel csetRayModel

/-! ### Why: the loop's denotation is infinite -/

/-- A successful run of the ray never decreases the state. -/
theorem le_of_runs_csetBody {a b : ULift.{0} ℕ}
    (h : Runs (fun x => (csetBody x).carrier) a b) : a.down ≤ b.down := by
  induction h with
  | done hs =>
      rcases hs with hs | hs
      · exact le_of_eq (congrArg ULift.down (Sum.inl.inj hs)).symm
      · exact absurd hs (by simp)
  | more hs _ ih =>
      rcases hs with hs | hs
      · exact absurd hs (by simp)
      · rcases Sum.inr.inj hs with rfl
        exact Nat.le_of_succ_le ih

/-- Every state at or above the start is reached. -/
theorem runs_csetBody_add (a : ULift.{0} ℕ) :
    ∀ k : ℕ, Runs (fun x => (csetBody x).carrier) a (ULift.up (a.down + k))
  | 0 => .done (Or.inl (by cases a; rfl))
  | k + 1 => .more (a' := ULift.up (a.down + 1)) (Or.inr rfl)
      (by simpa [Nat.add_assoc, Nat.add_comm 1 k] using
        runs_csetBody_add (ULift.up (a.down + 1)) k)

/-- **Reachability along the ray is exactly the upper set of the start.** -/
theorem runs_csetBody_iff {a b : ULift.{0} ℕ} :
    Runs (fun x => (csetBody x).carrier) a b ↔ a.down ≤ b.down := by
  constructor
  · exact le_of_runs_csetBody
  · intro h
    have := runs_csetBody_add a (b.down - a.down)
    rwa [Nat.add_sub_cancel' h, ULift.up_down] at this

/-- **The ray loop denotes an infinite set.**  This is the concrete obstruction
behind `finSet_not_alg_lambdaIter`: whatever the finite model would have to
assign to `iter x (step x)` at `x = n`, the countable model assigns the whole
upper set of `n`, which is infinite. -/
theorem csetLoop_infinite (ρ : csetRayModel.Env β₁) :
    (denote csetRayModel hloop ρ).carrier.Infinite := by
  rw [denote_hloop]
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => ULift.up (ρ.2.down + k)) ?_ ?_
  · intro i j hij
    have : ρ.2.down + i = ρ.2.down + j := congrArg ULift.down hij
    exact Nat.add_left_cancel this
  · intro k
    exact runs_csetBody_add ρ.2 k

end Isotope.LambdaIter.Monadic
