import Isotope.LambdaIter.Opsem.BigStep
import Isotope.LambdaIter.Subtyping.Semantics.Soundness

/-!
# Adequacy: the operational semantics *is* the `StateT S Part` denotation

Fix a `StateModel`, i.e. an abstract state set `S` together with a total,
deterministic transformer `run f : S → ⟦src f⟧ → S × ⟦trg f⟧` for each
instruction, subject to the purity law.  Two semantics are then available for
`λ_iter`:

* the big-step operational semantics `Eval` of
  `Isotope.LambdaIter.Opsem.BigStep`, and
* the denotational semantics `Isotope.LambdaIter.Subtyping.Semantics.denote` in the Elgot
  monad `PartState S = StateT S Part`, via the derived
  `instructionModelOfStateModel`.

This file proves they are the *same thing*: `eval_iff_denote` identifies the
evaluation relation with membership in the denotation, `diverges_iff_denote_none`
identifies operational divergence with denotational undefinedness, and
`observe_eq_denote` packages both as an equality of `Part`-valued observations —
the statement the thesis cites.

Two bookkeeping points recur throughout.

* `StateT S m A` unfolds to `S → m (A × S)`: the **value** comes first and the
  **state** second.  `StateModel.run`, and hence `observe`, use the opposite
  order `(state, value)`.  The translation between the two is `Prod.swap`, which
  is why `observe_eq_denote` is stated with a `Prod.swap <$> _`.
* Divergence is the only source of partiality: instructions are total, so the
  denotation of a program is undefined exactly when some `iter` unfolds forever.
  Accordingly the heart of the proof is `iterEval_iff_runs`, which matches the
  operational `IterEval` against `Isotope.Elgot.Part.Runs` — the inductive
  characterisation of the `Part`-level iteration operator.
-/

namespace Isotope.LambdaIter.Opsem

open Isotope.LambdaIter.Subtyping.Semantics
open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ] [TypeModel.{u, v} τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε] [Bot ε]
variable {S : Type v} [StateModel Φ τ ε S]
variable {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}

/-! ## Unfolding the denotation at a state

Every clause of `Isotope.LambdaIter.Subtyping.Semantics.denote`, specialised to
`PartState S` and applied to an initial state, is a `Part`-level bind.  Each of
the following holds by `rw [denote]` followed by `rfl`; they are the only place
where the `StateT` bind has to be unfolded. -/

/-- Denotation of a free variable, at a state. -/
theorem denote_fv_apply {x : ν} {A : τ} (hx : Γ.lookup x = some A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.fv (Φ := Φ) (β := β) hx) γ ρ s
      = Part.some (CtxDen.lookup γ x hx, s) := by
  rw [denote]; rfl

/-- Denotation of a bound variable, at a state. -/
theorem denote_bv_apply {ι : Fin n} (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε)
        (HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := ι)) γ ρ s
      = Part.some (BoundDen.get ρ ι, s) := by
  rw [denote]; rfl

/-- Denotation of the unit value, at a state. -/
theorem denote_unit_apply (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε)
        (HasType.unit (Φ := Φ) (Γ := Γ) (β := β)) γ ρ s
      = (Part.some (TypeModel.unitEquiv.symm (), s) :
          Part (TyDen (LambdaIter.unit : τ) × S)) := by
  rw [denote]; rfl

/-- Denotation of an instruction, at a state: the state model's transformer,
with the pair swapped into `StateT`'s `(value, state)` order. -/
theorem denote_op_apply {f : Φ} {a : Tm ν Φ n} (ha : HasType Φ Γ β a (instrSrc f))
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.op ha) γ ρ s
      = (denote (m := Elgot.PartState S) (ε := ε) ha γ ρ s).bind
          (fun p => Part.some (Prod.swap (StateModel.run (ε := ε) f p.2 p.1))) := by
  rw [denote]; rfl

/-- Denotation of a `let`, at a state. -/
theorem denote_let₁_apply {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B)
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.let₁ ha hb) γ ρ s
      = (denote (m := Elgot.PartState S) (ε := ε) ha γ ρ s).bind
          (fun p => denote (m := Elgot.PartState S) (ε := ε) hb γ (ρ, p.1) p.2) := by
  rw [denote]; rfl

/-- Denotation of a pair, at a state; components are evaluated left to right. -/
theorem denote_pair_apply {a b : Tm ν Φ n} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B)
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.pair ha hb) γ ρ s
      = ((denote (m := Elgot.PartState S) (ε := ε) ha γ ρ s).bind
          (fun p => (denote (m := Elgot.PartState S) (ε := ε) hb γ ρ p.2).bind
            (fun r => Part.some ((TypeModel.tensorEquiv A B).symm (p.1, r.1), r.2))) :
          Part (TyDen (LambdaIter.tensor A B) × S)) := by
  rw [denote]; rfl

/-- Denotation of a destructuring `let`, at a state. -/
theorem denote_let₂_apply {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
    (ha : HasType Φ Γ β a (LambdaIter.tensor A B))
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C)
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.let₂ ha hc) γ ρ s
      = (denote (m := Elgot.PartState S) (ε := ε) ha γ ρ s).bind
          (fun p => denote (m := Elgot.PartState S) (ε := ε) hc γ
            ((ρ, (TypeModel.tensorEquiv A B p.1).1),
              (TypeModel.tensorEquiv A B p.1).2) p.2) := by
  rw [denote]; rfl

/-- Denotation of a left injection, at a state. -/
theorem denote_inl_apply {a : Tm ν Φ n} {A B : τ} (ha : HasType Φ Γ β a A)
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.inl (B := B) ha) γ ρ s
      = ((denote (m := Elgot.PartState S) (ε := ε) ha γ ρ s).bind
          (fun p => Part.some ((TypeModel.coprodEquiv A B).symm (Sum.inl p.1), p.2)) :
          Part (TyDen (LambdaIter.coprod A B) × S)) := by
  rw [denote]; rfl

/-- Denotation of a right injection, at a state. -/
theorem denote_inr_apply {b : Tm ν Φ n} {A B : τ} (hb : HasType Φ Γ β b B)
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.inr (A := A) hb) γ ρ s
      = ((denote (m := Elgot.PartState S) (ε := ε) hb γ ρ s).bind
          (fun p => Part.some ((TypeModel.coprodEquiv A B).symm (Sum.inr p.1), p.2)) :
          Part (TyDen (LambdaIter.coprod A B) × S)) := by
  rw [denote]; rfl

/-- Denotation of an `abort`, at a state: the continuation is unreachable. -/
theorem denote_abort_apply {a : Tm ν Φ n} {C : τ}
    (ha : HasType Φ Γ β a LambdaIter.empty)
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.abort (C := C) ha) γ ρ s
      = (denote (m := Elgot.PartState S) (ε := ε) ha γ ρ s).bind
          (fun p => (Empty.elim (TypeModel.emptyEquiv p.1) :
            Elgot.PartState S (TyDen C)) p.2) := by
  rw [denote]; rfl

/-- Denotation of a `case`, at a state.  The branch is selected by a `match` on
the scrutinee's value, which only reduces once that value is known to be an
injection. -/
theorem denote_case_apply {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
    (he : HasType Φ Γ β e (LambdaIter.coprod A B))
    (hl : HasType Φ Γ (.snoc β A) l C) (hr : HasType Φ Γ (.snoc β B) r C)
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.case he hl hr) γ ρ s
      = (denote (m := Elgot.PartState S) (ε := ε) he γ ρ s).bind
          (fun p =>
            (match TypeModel.coprodEquiv A B p.1 with
              | .inl a => denote (m := Elgot.PartState S) (ε := ε) hl γ (ρ, a)
              | .inr b => denote (m := Elgot.PartState S) (ε := ε) hr γ (ρ, b)) p.2) := by
  rw [denote]; rfl

/-- Denotation of a subsumption, at a state. -/
theorem denote_sub_apply {a : Tm ν Φ n} {A B : τ} (ha : HasType Φ Γ β a A)
    (d : Subty A B) (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.sub ha d) γ ρ s
      = (denote (m := Elgot.PartState S) (ε := ε) ha γ ρ s).bind
          (fun p => Part.some (coeSub d p.1, p.2)) := by
  rw [denote]; rfl

/-! ## The loop body as a `Part`-level iteration body -/

/-- The `Part`-level iteration body of a `λ_iter` loop in a state model: run the
loop body on the current loop-carried value and state, then distribute the
resulting state over the returned sum.  This is exactly the body that
`Isotope.Elgot.StateT.instIterate` hands to `Part`'s iteration operator. -/
noncomputable def loopBody {b : Tm ν Φ (n + 1)} {A B : τ}
    (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) :
    TyDen A × S → Part ((TyDen B × S) ⊕ (TyDen A × S)) :=
  Elgot.StateT.body (S := S) (fun x =>
    denote (m := Elgot.PartState S) (ε := ε) hb γ (ρ, x) >>= fun w =>
      pure (TypeModel.coprodEquiv B A w))

/-- Denotation of a loop, at a state: evaluate the initial value, then iterate
`loopBody`. -/
theorem denote_iter_apply {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A))
    (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) (HasType.iter ha hb) γ ρ s
      = (denote (m := Elgot.PartState S) (ε := ε) ha γ ρ s).bind
          (fun p => Elgot.iter (loopBody (ε := ε) hb γ ρ) p) := by
  rw [denote]; rfl

/-- `loopBody`, written out as two successive `Part` binds. -/
theorem loopBody_eq {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    (γ : CtxDen Γ) (ρ : BoundDen β) (p : TyDen A × S) :
    loopBody (ε := ε) hb γ ρ p
      = ((denote (m := Elgot.PartState S) (ε := ε) hb γ (ρ, p.1) p.2).bind
          (fun r => Part.some (TypeModel.coprodEquiv B A r.1, r.2))).bind
          (fun r => Part.some (Elgot.StateT.distrib S r)) := rfl

/-- Distributing the state over a left injection. -/
@[simp] theorem distrib_inl {X Y : Type v} (x : X) (t : S) :
    Elgot.StateT.distrib S ((Sum.inl x : X ⊕ Y), t) = Sum.inl (x, t) := rfl

/-- Distributing the state over a right injection. -/
@[simp] theorem distrib_inr {X Y : Type v} (y : Y) (t : S) :
    Elgot.StateT.distrib S ((Sum.inr y : X ⊕ Y), t) = Sum.inr (y, t) := rfl

/-- Membership in `loopBody`: one execution of the loop body, with its state
distributed over the returned sum. -/
theorem mem_loopBody_iff {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    (γ : CtxDen Γ) (ρ : BoundDen β) (p : TyDen A × S)
    (z : (TyDen B × S) ⊕ (TyDen A × S)) :
    z ∈ loopBody (ε := ε) hb γ ρ p ↔
      ∃ (w : TyDen (LambdaIter.coprod B A)) (t : S),
        (w, t) ∈ denote (m := Elgot.PartState S) (ε := ε) hb γ (ρ, p.1) p.2 ∧
          z = Elgot.StateT.distrib S (TypeModel.coprodEquiv B A w, t) := by
  rw [loopBody_eq, Part.mem_bind_iff]
  constructor
  · rintro ⟨r, hr, hz⟩
    rw [Part.mem_bind_iff] at hr
    obtain ⟨r', hr', hrr⟩ := hr
    rw [Part.mem_some_iff] at hrr hz
    subst hrr
    exact ⟨r'.1, r'.2, hr', hz⟩
  · rintro ⟨w, t, hw, rfl⟩
    exact ⟨_, Part.mem_bind hw (Part.mem_some _), Part.mem_some _⟩

/-! ## Loops: `IterEval` is `Part.Runs` -/

section Iter

variable {b : Tm ν Φ (n + 1)} {A B : τ}
  {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
  {γ : CtxDen Γ} {ρ : BoundDen β}

/-- A successful operational run of a loop body is a successful `Part`-level
iteration run. -/
theorem IterEval.toRuns
    (ih : ∀ (y : TyDen A) (t t' : S) (w : TyDen (LambdaIter.coprod B A)),
      Eval (ε := ε) hb γ (ρ, y) t t' w →
        (w, t') ∈ denote (m := Elgot.PartState S) (ε := ε) hb γ (ρ, y) t) :
    {x : TyDen A} → {s s' : S} → {v : TyDen B} →
    IterEval (ε := ε) hb γ ρ x s s' v →
      Elgot.Part.Runs (loopBody (ε := ε) hb γ ρ) (x, s) (v, s')
  | _, _, _, _, .done hx hw =>
      Elgot.Part.Runs.done
        ((mem_loopBody_iff γ ρ _ _).2 ⟨_, _, ih _ _ _ _ hx, by rw [hw]; rfl⟩)
  | _, _, _, _, .more hx hw rest =>
      Elgot.Part.Runs.more
        ((mem_loopBody_iff γ ρ _ _).2 ⟨_, _, ih _ _ _ _ hx, by rw [hw]; rfl⟩)
        (IterEval.toRuns ih rest)

/-- A successful `Part`-level iteration run is a successful operational run of
the loop body. -/
theorem IterEval.ofRuns
    (ih : ∀ (y : TyDen A) (t t' : S) (w : TyDen (LambdaIter.coprod B A)),
      (w, t') ∈ denote (m := Elgot.PartState S) (ε := ε) hb γ (ρ, y) t →
        Eval (ε := ε) hb γ (ρ, y) t t' w) :
    ∀ {p : TyDen A × S} {z : TyDen B × S},
      Elgot.Part.Runs (loopBody (ε := ε) hb γ ρ) p z →
        IterEval (ε := ε) hb γ ρ p.1 p.2 z.2 z.1 := by
  intro p z hrun
  induction hrun with
  | @done p z hz =>
    obtain ⟨w, t, hw, hz⟩ := (mem_loopBody_iff γ ρ p _).1 hz
    cases hc : TypeModel.coprodEquiv B A w with
    | inl x =>
      rw [hc] at hz
      simp only [distrib_inl, Sum.inl.injEq] at hz
      subst hz
      exact .done (ih _ _ _ _ hw) hc
    | inr y =>
      rw [hc] at hz
      simp only [distrib_inr] at hz
      exact absurd hz (by simp)
  | @more p p' z hz _ hrest =>
    obtain ⟨w, t, hw, hz⟩ := (mem_loopBody_iff γ ρ p _).1 hz
    cases hc : TypeModel.coprodEquiv B A w with
    | inl x =>
      rw [hc] at hz
      simp only [distrib_inl] at hz
      exact absurd hz (by simp)
    | inr y =>
      rw [hc] at hz
      simp only [distrib_inr, Sum.inr.injEq] at hz
      subst hz
      exact .more (ih _ _ _ _ hw) hc hrest

/-- Operational loop runs and `Part`-level iteration runs coincide, given the
correspondence for the loop body. -/
theorem iterEval_iff_runs
    (ih : ∀ (y : TyDen A) (t t' : S) (w : TyDen (LambdaIter.coprod B A)),
      Eval (ε := ε) hb γ (ρ, y) t t' w ↔
        (w, t') ∈ denote (m := Elgot.PartState S) (ε := ε) hb γ (ρ, y) t)
    (x : TyDen A) (s s' : S) (v : TyDen B) :
    IterEval (ε := ε) hb γ ρ x s s' v ↔
      Elgot.Part.Runs (loopBody (ε := ε) hb γ ρ) (x, s) (v, s') :=
  ⟨IterEval.toRuns (fun y t t' w => (ih y t t' w).1),
    fun h => IterEval.ofRuns (fun y t t' w => (ih y t t' w).2) h⟩

end Iter

/-! ## Adequacy -/

/-- **Adequacy.**  A program typed by `h` evaluates, from state `s`, to state
`s'` with value `v` exactly when `(v, s')` is a possible result of its
denotation in `StateT S Part` started at `s`.

The two semantics are therefore literally the same partial function; in
particular the operational semantics of a state model *is* its denotational
semantics in the Elgot monad `PartState S`. -/
theorem eval_iff_denote {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) :
    ∀ (ρ : BoundDen β) (s s' : S) (v : TyDen A),
      Eval (ε := ε) h γ ρ s s' v ↔
        (v, s') ∈ denote (m := Elgot.PartState S) (ε := ε) h γ ρ s := by
  induction h with
  | fv hx =>
    intro ρ s s' v
    rw [denote_fv_apply, Part.mem_some_iff]
    constructor
    · intro he; cases he; rfl
    · intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .fv hx γ ρ _
  | bv =>
    intro ρ s s' v
    rw [denote_bv_apply, Part.mem_some_iff]
    constructor
    · intro he; cases he; rfl
    · intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .bv γ ρ _
  | unit =>
    intro ρ s s' v
    rw [denote_unit_apply, Part.mem_some_iff]
    constructor
    · intro he; cases he; rfl
    · intro he
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact .unit γ ρ _
  | op ha iha =>
    intro ρ s s' v
    rw [denote_op_apply, Part.mem_bind_iff]
    constructor
    · intro he
      cases he with
      | op hx hr =>
        refine ⟨(_, _), (iha _ _ _ _).1 hx, ?_⟩
        rw [Part.mem_some_iff]
        simp only [hr, Prod.swap]
    · rintro ⟨p, hp, hv⟩
      rw [Part.mem_some_iff] at hv
      exact .op ((iha _ _ _ _).2 hp) (by simpa using congrArg Prod.swap hv.symm)
  | let₁ ha hb iha ihb =>
    intro ρ s s' v
    rw [denote_let₁_apply, Part.mem_bind_iff]
    constructor
    · intro he
      cases he with
      | let₁ hx hy => exact ⟨(_, _), (iha _ _ _ _).1 hx, (ihb _ _ _ _).1 hy⟩
    · rintro ⟨p, hp, hv⟩
      exact .let₁ ((iha _ _ _ _).2 hp) ((ihb _ _ _ _).2 hv)
  | pair ha hb iha ihb =>
    intro ρ s s' v
    rw [denote_pair_apply]
    simp only [Part.mem_bind_iff, Part.mem_some_iff]
    constructor
    · intro he
      obtain ⟨s₁, x, y, hx, hy, rfl⟩ := he.inv
      exact ⟨(x, s₁), (iha _ _ _ _).1 hx, (y, s'), (ihb _ _ _ _).1 hy, rfl⟩
    · rintro ⟨p, hp, r, hr, hv⟩
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact .pair ((iha _ _ _ _).2 hp) ((ihb _ _ _ _).2 hr)
  | let₂ ha hc iha ihc =>
    intro ρ s s' v
    rw [denote_let₂_apply, Part.mem_bind_iff]
    constructor
    · intro he
      cases he with
      | let₂ hx hy => exact ⟨(_, _), (iha _ _ _ _).1 hx, (ihc _ _ _ _).1 hy⟩
    · rintro ⟨p, hp, hv⟩
      exact .let₂ ((iha _ _ _ _).2 hp) ((ihc _ _ _ _).2 hv)
  | inl ha iha =>
    intro ρ s s' v
    rw [denote_inl_apply]
    simp only [Part.mem_bind_iff, Part.mem_some_iff]
    constructor
    · intro he
      obtain ⟨x, hx, rfl⟩ := he.inv
      exact ⟨(x, s'), (iha _ _ _ _).1 hx, rfl⟩
    · rintro ⟨p, hp, hv⟩
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact .inl ((iha _ _ _ _).2 hp)
  | inr hb ihb =>
    intro ρ s s' v
    rw [denote_inr_apply]
    simp only [Part.mem_bind_iff, Part.mem_some_iff]
    constructor
    · intro he
      obtain ⟨y, hy, rfl⟩ := he.inv
      exact ⟨(y, s'), (ihb _ _ _ _).1 hy, rfl⟩
    · rintro ⟨p, hp, hv⟩
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact .inr ((ihb _ _ _ _).2 hp)
  | case he hl hr ihe ihl ihr =>
    intro ρ s s' v
    rw [denote_case_apply, Part.mem_bind_iff]
    constructor
    · intro hev
      cases hev with
      | caseL hx hw hy =>
        refine ⟨(_, _), (ihe _ _ _ _).1 hx, ?_⟩
        rw [(hw : TypeModel.coprodEquiv _ _ (Prod.fst (_, _)) = _)]
        exact (ihl _ _ _ _).1 hy
      | caseR hx hw hy =>
        refine ⟨(_, _), (ihe _ _ _ _).1 hx, ?_⟩
        rw [(hw : TypeModel.coprodEquiv _ _ (Prod.fst (_, _)) = _)]
        exact (ihr _ _ _ _).1 hy
    · rintro ⟨p, hp, hv⟩
      cases hw : TypeModel.coprodEquiv _ _ p.1 with
      | inl a =>
        rw [hw] at hv
        exact .caseL ((ihe _ _ _ _).2 hp) hw ((ihl _ _ _ _).2 hv)
      | inr b =>
        rw [hw] at hv
        exact .caseR ((ihe _ _ _ _).2 hp) hw ((ihr _ _ _ _).2 hv)
  | abort ha iha =>
    intro ρ s s' v
    rw [denote_abort_apply, Part.mem_bind_iff]
    constructor
    · intro he; cases he
    · rintro ⟨p, _, _⟩
      exact (TypeModel.emptyEquiv p.1).elim
  | iter ha hb iha ihb =>
    intro ρ s s' v
    rw [denote_iter_apply, Part.mem_bind_iff]
    constructor
    · intro he
      cases he with
      | iter hx hloop =>
        refine ⟨(_, _), (iha _ _ _ _).1 hx, ?_⟩
        rw [Elgot.Part.mem_iter_iff]
        exact IterEval.toRuns (fun y t t' w => (ihb (ρ, y) t t' w).1) hloop
    · rintro ⟨p, hp, hv⟩
      rw [Elgot.Part.mem_iter_iff] at hv
      exact .iter ((iha _ _ _ _).2 hp)
        (IterEval.ofRuns (fun y t t' w => (ihb (ρ, y) t t' w).2) hv)
  | sub ha d iha =>
    intro ρ s s' v
    rw [denote_sub_apply]
    simp only [Part.mem_bind_iff, Part.mem_some_iff]
    constructor
    · intro he
      cases he with
      | sub hx => exact ⟨(_, _), (iha _ _ _ _).1 hx, rfl⟩
    · rintro ⟨p, hp, hv⟩
      simp only [Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl⟩ := hv
      exact .sub ((iha _ _ _ _).2 hp)

/-- Adequacy, as an implication from the operational side. -/
theorem Eval.mem_denote {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} {v : TyDen A}
    (he : Eval (ε := ε) h γ ρ s s' v) :
    (v, s') ∈ denote (m := Elgot.PartState S) (ε := ε) h γ ρ s :=
  (eval_iff_denote h γ ρ s s' v).1 he

/-- Adequacy, as an implication from the denotational side. -/
theorem Eval.of_mem_denote {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} {v : TyDen A}
    (hv : (v, s') ∈ denote (m := Elgot.PartState S) (ε := ε) h γ ρ s) :
    Eval (ε := ε) h γ ρ s s' v :=
  (eval_iff_denote h γ ρ s s' v).2 hv

/-- **Operational divergence is denotational undefinedness.** -/
theorem diverges_iff_denote_not_dom {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    Diverges (ε := ε) h γ ρ s ↔
      ¬ (denote (m := Elgot.PartState S) (ε := ε) h γ ρ s).Dom := by
  constructor
  · intro hd hdom
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 hdom
    exact hd ⟨z.2, z.1, Eval.of_mem_denote hz⟩
  · rintro hd ⟨s', v, he⟩
    exact hd (Part.dom_iff_mem.2 ⟨(v, s'), he.mem_denote⟩)

/-- **Operational divergence is denotational undefinedness**, in `Part.none`
form. -/
theorem diverges_iff_denote_none {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    Diverges (ε := ε) h γ ρ s ↔
      denote (m := Elgot.PartState S) (ε := ε) h γ ρ s = Part.none := by
  rw [diverges_iff_denote_not_dom, Part.eq_none_iff]
  constructor
  · intro hd z hz
    exact hd (Part.dom_iff_mem.2 ⟨z, hz⟩)
  · intro hn hdom
    obtain ⟨z, hz⟩ := Part.dom_iff_mem.1 hdom
    exact hn z hz

/-! ## The packaged statement

`observe` returns `(state, value)` pairs, while `StateT` returns
`(value, state)`; the two observations therefore differ by exactly one
`Prod.swap`. -/

/-- **The operational outcome of a state model is its `StateT S Part`
denotation.**  This is the statement the thesis cites: for every state model,
every typing derivation, and every initial state, the operationally observed
outcome — the final state paired with the returned value, or divergence — is the
denotation in the Elgot monad `PartState S`, up to the `(state, value)` versus
`(value, state)` convention. -/
theorem observe_eq_denote {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    observe (ε := ε) h γ ρ s =
      Prod.swap <$> denote (m := Elgot.PartState S) (ε := ε) h γ ρ s := by
  apply Part.ext
  intro z
  rw [mem_observe_iff, Part.map_eq_map, Part.mem_map_iff]
  constructor
  · intro he
    exact ⟨(z.2, z.1), he.mem_denote, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact Eval.of_mem_denote hy

/-- The same statement, resolved for the denotation. -/
theorem denote_eq_observe {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
    denote (m := Elgot.PartState S) (ε := ε) h γ ρ s =
      Prod.swap <$> observe (ε := ε) h γ ρ s := by
  apply Part.ext
  intro z
  rw [Part.map_eq_map, Part.mem_map_iff]
  constructor
  · intro hz
    exact ⟨(z.2, z.1), (mem_observe_iff h γ ρ s _).2 (Eval.of_mem_denote hz), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ((mem_observe_iff h γ ρ s y).1 hy).mem_denote

/-- `observeClosed` is `observe` at the empty environments. -/
theorem observeClosed_eq {t : Tm Empty Φ 0} {A : τ}
    (h : HasType Φ (.nil : Ctx Empty τ) .nil t A) (s : S) :
    observeClosed (ε := ε) h s = observe (ε := ε) h PUnit.unit PUnit.unit s := rfl

/-- The closed-program form of `observe_eq_denote`. -/
theorem observeClosed_eq_denoteClosed {t : Tm Empty Φ 0} {A : τ}
    (h : HasType Φ (.nil : Ctx Empty τ) .nil t A) (s : S) :
    observeClosed (ε := ε) h s =
      Prod.swap <$> denoteClosed (m := Elgot.PartState S) (ε := ε) h s :=
  observe_eq_denote h PUnit.unit PUnit.unit s

/-- Closed programs with equal denotations are observationally
indistinguishable. -/
theorem obsEq_of_denoteClosed_eq {t₁ t₂ : Tm Empty Φ 0} {A : τ}
    {h₁ : HasType Φ (.nil : Ctx Empty τ) .nil t₁ A}
    {h₂ : HasType Φ (.nil : Ctx Empty τ) .nil t₂ A}
    (hd : denoteClosed (m := Elgot.PartState S) (ε := ε) h₁ =
      denoteClosed (m := Elgot.PartState S) (ε := ε) h₂) :
    ModelObsEq (ε := ε) (S := S) h₁ h₂ := fun s => by
  rw [observeClosed_eq_denoteClosed, observeClosed_eq_denoteClosed, hd]

/-- **Soundness of the equational theory for the operational semantics.**  Two
closed programs related by the proof-relevant typed equational theory are
observationally indistinguishable in *every* state model.  This is the
composition of `Isotope.LambdaIter.Subtyping.Semantics.sound` at `PartState S` with
adequacy. -/
theorem modelObsEq_of_deriv {t₁ t₂ : Tm Empty Φ 0} {A : τ}
    {h₁ : HasType Φ (.nil : Ctx Empty τ) .nil t₁ A}
    {h₂ : HasType Φ (.nil : Ctx Empty τ) .nil t₂ A}
    (d : TypedEquiv.Deriv (⊥ : ε) (.nil : Ctx Empty τ) h₁ h₂) :
    ModelObsEq (ε := ε) (S := S) h₁ h₂ :=
  obsEq_of_denoteClosed_eq
    (Subtyping.Semantics.sound (m := Elgot.PartState S) (ε := ε) d PUnit.unit PUnit.unit)

end Isotope.LambdaIter.Opsem
