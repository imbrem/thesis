import Isotope.Elgot.Effectful
import Isotope.LambdaIter.Opsem.Observation

/-!
# The verdict: soundness holds, completeness fails

This module settles the question the thesis asks about `λ_iter`: *are two
programs equivalent in the equational theory exactly when they are
observationally indistinguishable under every interpretation of the individual
operations?*  The answer is **no**: one implication holds and the other fails.

* **Soundness holds.**  If two typing derivations are related by the
  proof-relevant equational theory, then they are observationally equivalent in
  every state model, under every environment and from every initial state.  This
  is `Isotope.LambdaIter.Opsem.Observation.obsEq_of_related`, proved by
  instantiating the generic soundness theorem at the lawful Elgot monad
  `StateT S Part` and transporting along adequacy.

* **Completeness fails.**  `completeness_fails` below exhibits two closed
  programs over a signature with a single impure instruction `tick : 1 →_⊤ 1`,

  ```
  loop  = iter () { ι_r x : ι_r x }
  loopF = iter () { ι_r x : let _ = tick x; ι_r x }
  ```

  which diverge from every state in *every* state model (`loop_diverges`,
  `loopF_diverges`), hence are observationally equivalent
  (`loop_obsEq_loopF`), yet are **not** related by the equational theory
  (`loop_not_related`).

  A state model records only what an execution *ends with* -- its final state
  and returned value -- and neither program ever ends.  The effects `loopF`
  performs are all performed after the last moment a state model could look.
  The equational theory, by contrast, is sound for
  *every* lawful Elgot monad, including ones that observe more than the returned
  value.  `Isotope.Elgot.Eff` — a partial value paired with the proposition "an
  impure step was taken" — is such a monad, and it separates the two loops:
  `denoteClosed_loop_eff` gives `⟨Part.none, False⟩` while
  `denoteClosed_loopF_eff` gives `⟨Part.none, True⟩`.

* **What *is* preserved** is therefore finer than observation in state models:
  the invariant the equational theory really respects is equality of denotations
  in every lawful Elgot monad model of the signature
  (`Isotope.LambdaIter.Subtyping.Semantics.sound`), of which the state models
  `StateT S Part` are only a proper subclass.  Observational equivalence in
  state models forgets the effect trace of a divergent computation; the
  equational theory does not.

A separate, cheap observation is recorded at the end: `iter_not_pure` shows that
a loop built entirely from syntactically pure pieces is *not* semantically pure,
which is exactly why `Isotope.LambdaIter.LocallyNameless.Pure` omits a rule for
`iter`.
-/

namespace Isotope.LambdaIter.Opsem

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless
open Isotope.Elgot (Eff)

namespace Counterexample

open Example

/-! ## The two programs

The signature is the worked example of `Isotope.LambdaIter.Opsem.StateModel`:
`Instr.tick : unit →_impure unit` is an impure instruction of unit type, which
is the `f : 1 →_⊤ 1` the counterexample calls for. -/

/-- The empty free context: the counterexample programs are closed. -/
abbrev Γ0 : Ctx Empty (Ty Base) := .nil

/-- The empty bound context. -/
abbrev β0 : BoundCtx (Ty Base) 0 := .nil

/-- The silently diverging loop `iter () { ι_r x : ι_r x }`. -/
def loop : Tm Empty Instr 0 := .iter .unit (.inr (.bv 0))

/-- The noisily diverging loop `iter () { ι_r x : let _ = tick x; ι_r x }`. -/
def loopF : Tm Empty Instr 0 :=
  .iter .unit (.let₁ (.op .tick (.bv 0)) (.inr (.bv 1)))

/-- `loop` at the unit type.  Since the loop never returns, its result type is
unconstrained; it is stated at `unit` rather than at `empty` deliberately.  At
`empty` the statements below would be *vacuous*: `TyDen empty` is `Empty`, so
`Diverges` -- and with it half of `ObsEq` -- would hold for every derivation
whatsoever, for want of a value to return.  At `unit` the result type is
inhabited, so divergence and observational equivalence both have content. -/
def loopTy : HasType Instr Γ0 β0 loop Ty.unit :=
  .iter .unit (.inr HasType.newest)

/-- `loopF` at the unit type; see `loopTy` for why not at `empty`. -/
def loopFTy : HasType Instr Γ0 β0 loopF Ty.unit :=
  .iter .unit (.let₁ (.op HasType.newest) (.inr HasType.previous))

/-! ## Both loops diverge in every state model -/

/-- `loop` diverges in every state model, from every state. -/
theorem loop_diverges {S : Type} [StateModel Instr (Ty Base) Effect S]
    (γ : CtxDen Γ0) (ρ : BoundDen β0) (s : S) :
    Diverges (ε := Effect) loopTy γ ρ s := by
  apply Diverges.iter
  intro y t t' w z he
  exact he.inr_ne_inl

/-- `loopF` diverges in every state model, from every state: the impure
instruction runs, but the body still returns into the loop. -/
theorem loopF_diverges {S : Type} [StateModel Instr (Ty Base) Effect S]
    (γ : CtxDen Γ0) (ρ : BoundDen β0) (s : S) :
    Diverges (ε := Effect) loopFTy γ ρ s := by
  apply Diverges.iter
  intro y t t' w z he
  cases he with
  | let₁ _ h2 => exact h2.inr_ne_inl

/-- **The two loops are observationally indistinguishable.**  No state model,
environment or initial state separates them, because neither ever returns. -/
theorem loop_obsEq_loopF : Observation.ObsEq (ε := Effect) loopTy loopFTy := by
  refine Observation.obsEq_of_eval_iff (ε := Effect) ?_
  intro S _ γ ρ s s' v
  constructor
  · intro he; exact absurd ⟨s', v, he⟩ (loop_diverges (S := S) γ ρ s)
  · intro he; exact absurd ⟨s', v, he⟩ (loopF_diverges (S := S) γ ρ s)

/-! ## An effect-observing model of the instructions

`Isotope.Elgot.Eff` is a lawful Elgot monad which records, alongside the partial
result, whether an impure step was taken — including along a run that never
returns.  Interpreting the example signature in it is the refutation of
completeness. -/

/-- The `Eff`-valued denotation of the example instructions: the pure `succ`
performs no effect, while the impure `tick` returns the unit value and flags
that an effect was performed. -/
def denoteEff : (f : Instr) →
    TyDen (τ := Ty Base) (instrSrc f) → Eff (TyDen (τ := Ty Base) (instrTrg f))
  | .succ, a => pure (pureFnInstr .succ rfl a)
  | .tick, _ => ⟨Part.some (), True⟩

/-- The example signature, interpreted in the effect-observing monad. -/
instance instructionModelEff :
    InstructionModel Instr (Ty Base) Effect Eff where
  denote := denoteEff
  denotePure f hf := pureFnInstr f hf
  denote_pure
    | .succ, _, _ => rfl
    | .tick, hf, _ => absurd hf impure_ne_bot

/-- `tick` denotes an effectful computation returning the unit value. -/
theorem denoteEff_tick (a : TyDen (τ := Ty Base) (instrSrc Instr.tick)) :
    InstructionModel.denote (Φ := Instr) (τ := Ty Base) (ε := Effect) (m := Eff)
      Instr.tick a = ⟨Part.some (), True⟩ := rfl

/-- Binding after an effectful, immediately returning computation: the effect
flag is unconditionally raised. -/
theorem eff_some_bind {A B : Type} (u : A) (k : A → Eff B) :
    ((⟨Part.some u, True⟩ : Eff A) >>= k) = ⟨(k u).val, True⟩ := by
  apply Elgot.Eff.ext
  · rw [Elgot.Eff.val_bind, Part.bind_eq_bind, Part.bind_some]
  · exact propext ⟨fun _ => trivial, fun _ => Or.inl trivial⟩

/-- The newest bound variable, at the type index that `HasType.op` forces on it
inside `loopFTy`.  Stated separately because the syntactic type index there is
`instrSrc Instr.tick`, not the (definitionally equal) `unit` recorded in the
derivation, so the generic `denote_newest` does not match by rewriting. -/
theorem denote_newest_tick (γ : CtxDen Γ0) (ρ : BoundDen β0)
    (a : TyDen (τ := Ty Base) (LambdaIter.unit : Ty Base)) :
    denote (m := Eff) (ε := Effect) (A := instrSrc Instr.tick)
      (HasType.newest (Φ := Instr) (Γ := Γ0) (β := β0)
        (A := (LambdaIter.unit : Ty Base)))
      γ (ρ, a) = pure a :=
  denote_newest γ ρ a

/-- The `tick` step of `loopF` denotes an effectful computation returning the
unit value. -/
theorem denote_op_tick (γ : CtxDen Γ0) (ρ : BoundDen β0)
    (a : TyDen (τ := Ty Base) (LambdaIter.unit : Ty Base)) :
    denote (m := Eff) (ε := Effect)
      (HasType.op (f := Instr.tick)
        (HasType.newest (Φ := Instr) (Γ := Γ0) (β := β0)
          (A := (LambdaIter.unit : Ty Base))))
      γ (ρ, a)
      = (⟨Part.some (), True⟩ : Eff (TyDen (τ := Ty Base) (instrTrg Instr.tick))) := by
  rw [Subtyping.Semantics.denote.eq_3, denote_newest_tick]
  exact pure_bind _ _

/-- **`loop` diverges silently.**  Its `Eff` denotation records no effect. -/
theorem denoteClosed_loop_eff :
    denoteClosed (m := Eff) (ε := Effect) loopTy = ⟨Part.none, False⟩ := by
  unfold denoteClosed loopTy loop
  rw [Subtyping.Semantics.denote.eq_12, Subtyping.Semantics.denote.eq_5]
  simp only [Subtyping.Semantics.denote.eq_9, denote_newest, pure_bind,
    Equiv.apply_symm_apply]
  exact Elgot.Eff.iter_forever_pure _

/-- **`loopF` diverges noisily.**  Its `Eff` denotation has the same empty
partial value as `loop`, but records that an effect was performed. -/
theorem denoteClosed_loopF_eff :
    denoteClosed (m := Eff) (ε := Effect) loopFTy = ⟨Part.none, True⟩ := by
  unfold denoteClosed loopFTy loopF
  rw [Subtyping.Semantics.denote.eq_12, Subtyping.Semantics.denote.eq_5]
  simp only [Subtyping.Semantics.denote.eq_4, Subtyping.Semantics.denote.eq_9,
    denote_previous, denote_op_tick, pure_bind, eff_some_bind,
    Elgot.Eff.val_pure, Equiv.apply_symm_apply]
  exact Elgot.Eff.iter_forever_effectful _

/-- The two loops receive different denotations in the effect-observing
model. -/
theorem denoteClosed_eff_ne :
    denoteClosed (m := Eff) (ε := Effect) loopTy
      ≠ denoteClosed (m := Eff) (ε := Effect) loopFTy := by
  rw [denoteClosed_loop_eff, denoteClosed_loopF_eff]
  intro h
  exact (congrArg Elgot.Eff.ran h).mpr trivial

/-! ## The equational theory does not relate them -/

/-- **The equational theory does not prove the two loops equal.**  Were there a
derivation, generic soundness at the lawful Elgot monad `Eff` would force their
`Eff` denotations to agree, but those denotations differ in their effect
flag. -/
theorem loop_not_related :
    ¬ TypedEquiv.Related (⊥ : Effect) Γ0 loopTy loopFTy := by
  intro h
  have hd : denoteClosed (m := Eff) (ε := Effect) loopTy
      = denoteClosed (m := Eff) (ε := Effect) loopFTy :=
    Subtyping.Semantics.related_sound (m := Eff) (ε := Effect) h PUnit.unit PUnit.unit
  exact denoteClosed_eff_ne hd

/-- **Completeness fails.**  The converse of
`Isotope.LambdaIter.Opsem.Observation.obsEq_of_related` is false: observational
equivalence in every state model does not imply derivability in the equational
theory.  The witnesses are `loop_obsEq_loopF` and `loop_not_related`. -/
theorem completeness_fails :
    ¬ ∀ (a b : Tm Empty Instr 0) (A : Ty Base)
        (ha : HasType Instr Γ0 β0 a A) (hb : HasType Instr Γ0 β0 b A),
        Observation.ObsEq (ε := Effect) ha hb →
          TypedEquiv.Related (⊥ : Effect) Γ0 ha hb :=
  fun h => loop_not_related (h loop loopF Ty.unit loopTy loopFTy loop_obsEq_loopF)

/-! ## The observation is not vacuous

`ObsEq` quantifies over every state model of the signature.  For a signature
admitting *no* state model at all -- for instance one with a `⊥`-effect
instruction `unit → empty`, whose `pureFn` field cannot be inhabited -- that
quantification is empty and `ObsEq` degenerates to `True`.  The example
signature is not such a signature: `Example.instStateModel` is a state model on
`Nat`, and the two programs below are *separated* by it.  So
`Observation.obsEq_of_related` has real content here, and `loop_obsEq_loopF` is
a genuine coincidence of observations rather than an artefact of an empty
quantifier. -/

/-- The trivial program `()`. -/
def unitTm : Tm Empty Instr 0 := .unit

/-- The program `let _ = tick (); ()`.  It returns the same value as `unitTm`,
so only the *state* can tell the two apart. -/
def tickTm : Tm Empty Instr 0 := .let₁ (.op Instr.tick .unit) .unit

/-- `()` at the unit type. -/
def unitTmTy : HasType Instr Γ0 β0 unitTm Ty.unit := .unit

/-- `let _ = tick (); ()` at the unit type. -/
def tickTmTy : HasType Instr Γ0 β0 tickTm Ty.unit :=
  .let₁ (.op (f := Instr.tick) .unit) .unit

/-- Running `let _ = tick (); ()` bumps the state by one. -/
theorem eval_tickTm_succ {s s' : Nat}
    {v : TyDen (τ := Ty Base) (Ty.unit : Ty Base)}
    (h : Eval (ε := Effect) tickTmTy PUnit.unit PUnit.unit s s' v) :
    s' = s + 1 := by
  cases h with
  | let₁ hx hy =>
    cases hy with
    | unit _ _ _ =>
      cases hx with
      | op ha hr =>
        cases ha with
        | unit _ _ _ => exact (congrArg Prod.fst hr).symm

/-- Running `()` leaves the state alone. -/
theorem eval_unitTm (s : Nat) :
    Eval (ε := Effect) unitTmTy PUnit.unit PUnit.unit s s
      (TypeModel.unitEquiv.symm ()) :=
  .unit _ _ _

/-- **Observational equivalence is refutable at this signature.**  `()` and
`let _ = tick (); ()` return the same value but leave different final states, so
the `Nat` state model separates them.  This is what rules out the degenerate
reading of `ObsEq` under which soundness would hold for free -- and it is also
why the observation must record the final *state* and not merely the returned
value, since `trg tick = 1` carries no information. -/
theorem obsEq_refutable :
    ¬ Observation.ObsEq (ε := Effect) unitTmTy tickTmTy := by
  intro h
  have hEv := ((h Nat PUnit.unit PUnit.unit 0).1 0
    (TypeModel.unitEquiv.symm ())).1 (eval_unitTm 0)
  exact absurd (eval_tickTm_succ hEv) (by omega)

/-! ## Why `Pure` omits `iter`

`Isotope.LambdaIter.LocallyNameless.Pure` has no constructor for `iter`, so no
loop is ever syntactically pure — not even a loop all of whose subterms are.
The following shows that this is forced: the body and the initial value of
`loop` are pure, but `loop` itself does not denote a `pure` value in the
partiality monad, since it denotes nothing at all.  Were `iter` allowed into
`Pure` — as it would be by a "complete" effect signature declaring `⊥`
iterative — the pure-substitution rule `letBeta`, which relies on
`Isotope.LambdaIter.Subtyping.Semantics.denote_pure_factor` to duplicate and reorder pure
subterms, would become unsound. -/

/-- The `Part`-valued denotation of the example instructions.  Only the returned
value is observed, so `tick` is interpreted exactly like a pure instruction. -/
def denotePart : (f : Instr) →
    TyDen (τ := Ty Base) (instrSrc f) → Part (TyDen (τ := Ty Base) (instrTrg f))
  | .succ, a => pure (pureFnInstr .succ rfl a)
  | .tick, _ => Part.some ()

/-- The example signature, interpreted in the bare partiality monad. -/
instance instructionModelPart :
    InstructionModel Instr (Ty Base) Effect Part where
  denote := denotePart
  denotePure f hf := pureFnInstr f hf
  denote_pure
    | .succ, _, _ => rfl
    | .tick, hf, _ => absurd hf impure_ne_bot

/-- The initial value of `loop` is syntactically pure. -/
theorem loop_init_pure : Pure (⊥ : Effect) (Tm.unit : Tm Empty Instr 0) := .unit

/-- The body of `loop` is syntactically pure. -/
theorem loop_body_pure :
    Pure (⊥ : Effect) (Tm.inr (Tm.bv 0) : Tm Empty Instr 1) := .inr .bv

/-- `loop` itself is not syntactically pure: `Pure` has no rule for `iter`. -/
theorem loop_not_pure : ¬ Pure (⊥ : Effect) loop := by
  intro h
  unfold loop at h
  cases h

/-- `loop` denotes the empty partial value. -/
theorem denoteClosed_loop_part :
    denoteClosed (m := Part) (ε := Effect) loopTy = Part.none := by
  unfold denoteClosed loopTy loop
  rw [Subtyping.Semantics.denote.eq_12, Subtyping.Semantics.denote.eq_5]
  simp only [Subtyping.Semantics.denote.eq_9, denote_newest, pure_bind,
    Equiv.apply_symm_apply]
  exact Elgot.Part.iter_forever _

/-- **A loop of pure pieces is not semantically pure.**  Both the initial value
and the body of `loop` are syntactically pure (`loop_init_pure`,
`loop_body_pure`), yet `loop` does not denote a `pure` value: the conclusion of
`Isotope.LambdaIter.Subtyping.Semantics.denote_pure_factor` fails for it.  This is exactly
why `Pure` must omit `iter`, and why declaring `⊥` iterative would break
`letBeta`. -/
theorem iter_not_pure (v : TyDen (τ := Ty Base) (Ty.unit : Ty Base)) :
    denoteClosed (m := Part) (ε := Effect) loopTy ≠ (pure v : Part _) := by
  intro h
  rw [denoteClosed_loop_part] at h
  have hv : v ∈ (Part.none : Part (TyDen (τ := Ty Base) (Ty.unit : Ty Base))) := by
    rw [h]; exact Part.mem_some v
  exact Part.notMem_none v hv

end Counterexample

end Isotope.LambdaIter.Opsem
