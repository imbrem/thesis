import Isotope.LambdaIter.Opsem.StateModel

/-!
# A big-step operational semantics for `λ_iter`

Fix a `StateModel`: an abstract state set `S` together with a total,
deterministic transformer `run f : S → ⟦src f⟧ → S × ⟦trg f⟧` for every
instruction.  This file gives `λ_iter` a big-step operational semantics
relative to that datum.

The evaluation relation is indexed by a *typing derivation* and by *semantic
environments*, not by a raw term and a syntactic substitution.  That is the
presentation which can be compared with `Isotope.LambdaIter.Subtyping.Semantics.denote`:
the denotation is likewise a function of a derivation and of environments
`γ : CtxDen Γ`, `ρ : BoundDen β`, and subtyping is proof-relevant, so the
derivation genuinely matters (at `sub`).  A term-rewriting presentation would
have to re-derive typing at each step and would not see the coercions at all.

There is exactly one constructor per typing rule, with two exceptions.

* `case` has two constructors, `caseL` and `caseR`, one per branch taken.
  These are the two *evaluation* rules of the single typing rule.
* `abort` has **no** constructor, and this is forced: an `abort` derivation
  `HasType.abort ha` requires `ha : HasType Φ Γ β a empty`, so any rule for it
  would have to produce an inhabitant of `TyDen (empty : τ) ≃ Empty` before it
  could proceed.  So `abort a` never evaluates.  Note that this is *not*
  stuckness in the usual sense: a well-typed closed term of empty type does not
  exist, and in an open context the failure is inherited from the subterm `a`,
  which itself can never return.  Operationally, `abort` diverges exactly when
  its argument does, and there is nothing else it could do.  This matches
  `denote`, whose `abort` clause is `denote ha γ ρ >>= fun z => Empty.elim …`:
  the continuation is never reached.

Iteration is handled by the auxiliary relation `IterEval`, which mirrors
`Isotope.Elgot.Part.Runs`: a finite sequence of body executions, each returning
`ι_r` and threading its state into the next, terminating in a body execution
that returns `ι_l`.  Divergence is the *absence* of such a sequence.  This is
the whole source of partiality in `λ_iter`: instructions are total by the
definition of `StateModel`, so a program fails to return only by looping
forever.
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

/-! ## The evaluation relation -/

mutual

/-- Big-step evaluation.  `Eval h γ ρ s s' v` reads: under the free environment
`γ` and the bound environment `ρ`, starting from state `s`, the term typed by
`h` terminates in state `s'` with value `v`.

State is threaded strictly left-to-right, exactly as `denote` sequences its
binds. -/
inductive Eval : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
    CtxDen Γ → BoundDen β → S → S → TyDen A → Prop
  /-- A free variable is looked up in the free environment; the state is
  untouched. -/
  | fv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {x : ν} {A : τ}
      (hx : Γ.lookup x = some A) (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
      Eval (HasType.fv (Φ := Φ) (β := β) hx) γ ρ s s (CtxDen.lookup γ x hx)
  /-- A bound variable is looked up in the bound environment; the state is
  untouched. -/
  | bv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {ι : Fin n}
      (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
      Eval (HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := ι)) γ ρ s s
        (BoundDen.get ρ ι)
  /-- An instruction first evaluates its argument, then runs the state model's
  transformer on the resulting state and value. -/
  | op {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {f : Φ} {a : Tm ν Φ n}
      {ha : HasType Φ Γ β a (instrSrc f)}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {x : TyDen (τ := τ) (instrSrc f)} {v : TyDen (τ := τ) (instrTrg f)}
      (hx : Eval ha γ ρ s s₁ x)
      (hr : StateModel.run (ε := ε) f s₁ x = (s', v)) :
      Eval (HasType.op ha) γ ρ s s' v
  /-- `let` evaluates its bound term, extends the bound environment, and
  continues in the resulting state. -/
  | let₁ {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ (.snoc β A) b B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {x : TyDen A} {v : TyDen B}
      (hx : Eval ha γ ρ s s₁ x) (hy : Eval hb γ (ρ, x) s₁ s' v) :
      Eval (HasType.let₁ ha hb) γ ρ s s' v
  /-- The unit value is returned immediately. -/
  | unit {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) :
      Eval (HasType.unit (Φ := Φ) (Γ := Γ) (β := β)) γ ρ s s
        (TypeModel.unitEquiv.symm ())
  /-- A pair evaluates its components left-to-right. -/
  | pair {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A B : τ}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {x : TyDen A} {y : TyDen B}
      (hx : Eval ha γ ρ s s₁ x) (hy : Eval hb γ ρ s₁ s' y) :
      Eval (HasType.pair ha hb) γ ρ s s'
        ((TypeModel.tensorEquiv A B).symm (x, y))
  /-- A destructuring `let` evaluates its scrutinee and splits the result. -/
  | let₂ {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
      {ha : HasType Φ Γ β a (LambdaIter.tensor A B)}
      {hc : HasType Φ Γ (.snoc (.snoc β A) B) c C}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {p : TyDen (LambdaIter.tensor A B)} {v : TyDen C}
      (hx : Eval ha γ ρ s s₁ p)
      (hy : Eval hc γ
        ((ρ, (TypeModel.tensorEquiv A B p).1), (TypeModel.tensorEquiv A B p).2)
        s₁ s' v) :
      Eval (HasType.let₂ ha hc) γ ρ s s' v
  /-- Left injection. -/
  | inl {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A B : τ}
      {ha : HasType Φ Γ β a A}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} {x : TyDen A}
      (hx : Eval ha γ ρ s s' x) :
      Eval (HasType.inl (B := B) ha) γ ρ s s'
        ((TypeModel.coprodEquiv A B).symm (Sum.inl x))
  /-- Right injection. -/
  | inr {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {b : Tm ν Φ n} {A B : τ}
      {hb : HasType Φ Γ β b B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} {y : TyDen B}
      (hy : Eval hb γ ρ s s' y) :
      Eval (HasType.inr (A := A) hb) γ ρ s s'
        ((TypeModel.coprodEquiv A B).symm (Sum.inr y))
  /-- `case`, left branch. -/
  | caseL {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
      {he : HasType Φ Γ β e (LambdaIter.coprod A B)}
      {hl : HasType Φ Γ (.snoc β A) l C} {hr : HasType Φ Γ (.snoc β B) r C}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {w : TyDen (LambdaIter.coprod A B)} {x : TyDen A} {v : TyDen C}
      (hx : Eval he γ ρ s s₁ w)
      (hw : TypeModel.coprodEquiv A B w = Sum.inl x)
      (hy : Eval hl γ (ρ, x) s₁ s' v) :
      Eval (HasType.case he hl hr) γ ρ s s' v
  /-- `case`, right branch. -/
  | caseR {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)} {A B C : τ}
      {he : HasType Φ Γ β e (LambdaIter.coprod A B)}
      {hl : HasType Φ Γ (.snoc β A) l C} {hr : HasType Φ Γ (.snoc β B) r C}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {w : TyDen (LambdaIter.coprod A B)} {y : TyDen B} {v : TyDen C}
      (hx : Eval he γ ρ s s₁ w)
      (hw : TypeModel.coprodEquiv A B w = Sum.inr y)
      (hy : Eval hr γ (ρ, y) s₁ s' v) :
      Eval (HasType.case he hl hr) γ ρ s s' v
  /-- A loop evaluates its initial value and then performs a finite,
  successful run of its body. -/
  | iter {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
      {ha : HasType Φ Γ β a A}
      {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s' : S}
      {x : TyDen A} {v : TyDen B}
      (hx : Eval ha γ ρ s s₁ x)
      (hloop : IterEval hb γ ρ x s₁ s' v) :
      Eval (HasType.iter ha hb) γ ρ s s' v
  /-- Subsumption applies the coercion denoted by the subtyping derivation. -/
  | sub {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {a : Tm ν Φ n} {A B : τ}
      {ha : HasType Φ Γ β a A} {d : Subty A B}
      {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} {x : TyDen A}
      (hx : Eval ha γ ρ s s' x) :
      Eval (HasType.sub ha d) γ ρ s s' (coeSub d x)

/-- A finite successful run of a loop body, mirroring
`Isotope.Elgot.Part.Runs`.  `IterEval hb γ ρ x s s' v` reads: starting the body
`hb` with loop-carried value `x` in state `s`, finitely many `ι_r`-returning
iterations are followed by an `ι_l`-returning one, ending in state `s'` with
result `v`. -/
inductive IterEval : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {b : Tm ν Φ (n + 1)} → {A B : τ} →
    HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A) →
    CtxDen Γ → BoundDen β → TyDen A → S → S → TyDen B → Prop
  /-- The body returned `ι_l`: the loop stops. -/
  | done {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {b : Tm ν Φ (n + 1)} {A B : τ}
      {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
      {γ : CtxDen Γ} {ρ : BoundDen β} {x : TyDen A} {s s' : S}
      {w : TyDen (LambdaIter.coprod B A)} {v : TyDen B}
      (hx : Eval hb γ (ρ, x) s s' w)
      (hw : TypeModel.coprodEquiv B A w = Sum.inl v) :
      IterEval hb γ ρ x s s' v
  /-- The body returned `ι_r`: the loop continues with the new value and the
  new state. -/
  | more {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
      {b : Tm ν Φ (n + 1)} {A B : τ}
      {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
      {γ : CtxDen Γ} {ρ : BoundDen β} {x x' : TyDen A} {s s₁ s' : S}
      {w : TyDen (LambdaIter.coprod B A)} {v : TyDen B}
      (hx : Eval hb γ (ρ, x) s s₁ w)
      (hw : TypeModel.coprodEquiv B A w = Sum.inr x')
      (rest : IterEval hb γ ρ x' s₁ s' v) :
      IterEval hb γ ρ x s s' v

end

/-! ## Inversion at the compound-typed rules

`pair`, `inl` and `inr` are the three rules whose *conclusion type* is a
compound type former, `tensor A B` or `coprod A B`.  Inverting `Eval` at such a
rule with the `cases` tactic is impossible: `TypeFormers.tensor` is an abstract
class operation, not a constructor, so the dependent pattern matcher cannot
recover `A` and `B` from the type index and reports
`Failed to solve equation … tensor A B = tensor A' B'`.  Recursion on the
*typing derivation* — where the result type is still a variable — sidesteps the
problem, so we package the inversion payload as a predicate computed from the
derivation and prove it once. -/

/-- The inversion payload of an evaluation, for the three rules whose
conclusion type is a compound type former; `True` elsewhere, where the `cases`
tactic already suffices. -/
def Eval.Inv : {Γ : Ctx ν τ} → {n : Nat} → {β : BoundCtx τ n} →
    {t : Tm ν Φ n} → {A : τ} → HasType Φ Γ β t A →
    CtxDen Γ → BoundDen β → S → S → TyDen A → Prop
  | _, _, _, _, _, .pair ha hb, γ, ρ, s, s', v =>
      ∃ s₁ x y, Eval (ε := ε) ha γ ρ s s₁ x ∧ Eval (ε := ε) hb γ ρ s₁ s' y ∧
        v = (TypeModel.tensorEquiv _ _).symm (x, y)
  | _, _, _, _, _, .inl ha, γ, ρ, s, s', v =>
      ∃ x, Eval (ε := ε) ha γ ρ s s' x ∧
        v = (TypeModel.coprodEquiv _ _).symm (Sum.inl x)
  | _, _, _, _, _, .inr hb, γ, ρ, s, s', v =>
      ∃ y, Eval (ε := ε) hb γ ρ s s' y ∧
        v = (TypeModel.coprodEquiv _ _).symm (Sum.inr y)
  | _, _, _, _, _, _, _, _, _, _, _ => True

/-- Every evaluation satisfies its inversion payload. -/
theorem Eval.inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S} {v : TyDen A} :
    Eval (ε := ε) h γ ρ s s' v → Eval.Inv (ε := ε) h γ ρ s s' v
  | .pair hx hy => ⟨_, _, _, hx, hy, rfl⟩
  | .inl hx => ⟨_, hx, rfl⟩
  | .inr hy => ⟨_, hy, rfl⟩
  | .fv .. => trivial
  | .bv .. => trivial
  | .unit .. => trivial
  | .op .. => trivial
  | .let₁ .. => trivial
  | .let₂ .. => trivial
  | .caseL .. => trivial
  | .caseR .. => trivial
  | .iter .. => trivial
  | .sub .. => trivial

/-- Inversion for `pair`. -/
theorem Eval.pair_inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a b : Tm ν Φ n} {A B : τ}
    {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b B}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
    {v : TyDen (LambdaIter.tensor A B)}
    (he : Eval (ε := ε) (HasType.pair ha hb) γ ρ s s' v) :
    ∃ s₁ x y, Eval (ε := ε) ha γ ρ s s₁ x ∧ Eval (ε := ε) hb γ ρ s₁ s' y ∧
      v = (TypeModel.tensorEquiv A B).symm (x, y) := he.inv

/-- Inversion for `inl`. -/
theorem Eval.inl_inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {A B : τ} {ha : HasType Φ Γ β a A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
    {v : TyDen (LambdaIter.coprod A B)}
    (he : Eval (ε := ε) (HasType.inl (B := B) ha) γ ρ s s' v) :
    ∃ x, Eval (ε := ε) ha γ ρ s s' x ∧
      TypeModel.coprodEquiv A B v = Sum.inl x := by
  obtain ⟨x, hx, rfl⟩ := he.inv
  exact ⟨x, hx, Equiv.apply_symm_apply _ _⟩

/-- Inversion for `inr`. -/
theorem Eval.inr_inv {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ n} {A B : τ} {hb : HasType Φ Γ β b B}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
    {v : TyDen (LambdaIter.coprod A B)}
    (he : Eval (ε := ε) (HasType.inr (A := A) hb) γ ρ s s' v) :
    ∃ y, Eval (ε := ε) hb γ ρ s s' y ∧
      TypeModel.coprodEquiv A B v = Sum.inr y := by
  obtain ⟨y, hy, rfl⟩ := he.inv
  exact ⟨y, hy, Equiv.apply_symm_apply _ _⟩

/-- A term of the form `ι_r b` never evaluates to a left injection. -/
theorem Eval.inr_ne_inl {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ n} {A B : τ} {hb : HasType Φ Γ β b B}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s' : S}
    {v : TyDen (LambdaIter.coprod A B)} {z : TyDen A}
    (he : Eval (ε := ε) (HasType.inr (A := A) hb) γ ρ s s' v) :
    TypeModel.coprodEquiv A B v ≠ Sum.inl z := by
  obtain ⟨y, _, hy⟩ := he.inr_inv
  rw [hy]
  exact fun hc ↦ absurd hc (by simp)

/-! ## Determinism

Evaluation is a partial function: instructions are total and deterministic by
the definition of a state model, and every other rule is deterministic by
construction, so both the final state and the returned value are unique. -/

mutual

/-- Big-step evaluation is deterministic in both the final state and the
returned value. -/
theorem Eval.deterministic {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A}
    {γ : CtxDen Γ} {ρ : BoundDen β} {s s₁ s₂ : S} {v₁ v₂ : TyDen A} :
    Eval (ε := ε) h γ ρ s s₁ v₁ → Eval (ε := ε) h γ ρ s s₂ v₂ →
      s₁ = s₂ ∧ v₁ = v₂
  | .fv .., h₂ => by cases h₂; exact ⟨rfl, rfl⟩
  | .bv .., h₂ => by cases h₂; exact ⟨rfl, rfl⟩
  | .unit .., h₂ => by cases h₂; exact ⟨rfl, rfl⟩
  | .op hx hr, h₂ => by
      cases h₂ with
      | op hx' hr' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        have e := hr.symm.trans hr'
        exact ⟨congrArg Prod.fst e, congrArg Prod.snd e⟩
  | .let₁ hx hy, h₂ => by
      cases h₂ with
      | let₁ hx' hy' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        exact Eval.deterministic hy hy'
  | .pair hx hy, h₂ => by
      obtain ⟨_, _, _, hx', hy', rfl⟩ := h₂.inv
      obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
      obtain ⟨rfl, rfl⟩ := Eval.deterministic hy hy'
      exact ⟨rfl, rfl⟩
  | .let₂ hx hy, h₂ => by
      cases h₂ with
      | let₂ hx' hy' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        exact Eval.deterministic hy hy'
  | .inl hx, h₂ => by
      obtain ⟨_, hx', rfl⟩ := h₂.inv
      obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
      exact ⟨rfl, rfl⟩
  | .inr hy, h₂ => by
      obtain ⟨_, hy', rfl⟩ := h₂.inv
      obtain ⟨rfl, rfl⟩ := Eval.deterministic hy hy'
      exact ⟨rfl, rfl⟩
  | .caseL hx hw hy, h₂ => by
      cases h₂ with
      | caseL hx' hw' hy' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        cases Sum.inl.inj (hw.symm.trans hw')
        exact Eval.deterministic hy hy'
      | caseR hx' hw' hy' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        exact absurd (hw.symm.trans hw') (by simp)
  | .caseR hx hw hy, h₂ => by
      cases h₂ with
      | caseL hx' hw' hy' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        exact absurd (hw.symm.trans hw') (by simp)
      | caseR hx' hw' hy' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        cases Sum.inr.inj (hw.symm.trans hw')
        exact Eval.deterministic hy hy'
  | .iter hx hloop, h₂ => by
      cases h₂ with
      | iter hx' hloop' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        exact IterEval.deterministic hloop hloop'
  | .sub hx, h₂ => by
      cases h₂ with
      | sub hx' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        exact ⟨rfl, rfl⟩

/-- A successful loop run is deterministic in both the final state and the
returned value. -/
theorem IterEval.deterministic {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β} {x : TyDen A} {s s₁ s₂ : S}
    {v₁ v₂ : TyDen B} :
    IterEval (ε := ε) hb γ ρ x s s₁ v₁ → IterEval (ε := ε) hb γ ρ x s s₂ v₂ →
      s₁ = s₂ ∧ v₁ = v₂
  | .done hx hw, h₂ => by
      cases h₂ with
      | done hx' hw' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        exact ⟨rfl, Sum.inl.inj (hw.symm.trans hw')⟩
      | more hx' hw' rest' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        exact absurd (hw.symm.trans hw') (by simp)
  | .more hx hw rest, h₂ => by
      cases h₂ with
      | done hx' hw' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        exact absurd (hw.symm.trans hw') (by simp)
      | more hx' hw' rest' =>
        obtain ⟨rfl, rfl⟩ := Eval.deterministic hx hx'
        cases Sum.inr.inj (hw.symm.trans hw')
        exact IterEval.deterministic rest rest'

end

/-! ## Divergence and the induced observation

Determinism says evaluation is a *partial function*, so a program run from a
state has exactly one of two outcomes: it terminates, in which case both the
final state and the returned value are determined, or it diverges.  We package
this as a `Part (S × TyDen A)`, whose three cases are exactly the three
outcomes: `Part.some (s', v)`, and `Part.none` for divergence.

**Both components of the pair are needed.**  Observing only the returned value
identifies programs that are operationally different: take an instruction
`f : 1 →_⊤ 1` whose state transformer is not the identity — the `tick` of
`Isotope.LambdaIter.Opsem.Example`, say, with `S = Nat` and
`run tick s () = (s + 1, ())`.  Then `()` and `let _ = f (); ()` both return the
unique element of `TyDen (unit : τ)` from every state, so they are
indistinguishable by their values alone, yet they are distinguished by their
final states.  Since `trg f = 1` for such an `f`, no amount of *value*
observation can see the effect; the state must be observed too.  Conversely,
observing the final state alone is not enough either, because a program of type
`A ⊗ B` may compute a value without touching the state.  The pair is the right
observation. -/

/-- A program *diverges* from `s` when it has no evaluation at all: no final
state and no returned value.  Since instructions are total, this happens
exactly when some `iter` unfolds forever, or when an `abort` is reached — and
an `abort` is reached only if its own argument, of empty type, returned. -/
def Diverges {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β t A) (γ : CtxDen Γ) (ρ : BoundDen β) (s : S) : Prop :=
  ¬ ∃ s' v, Eval (ε := ε) h γ ρ s s' v

/-- The observation induced by the operational semantics: the final state
paired with the returned value, or `Part.none` for divergence.  This is
single-valued by `Eval.deterministic`. -/
noncomputable def observe {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) (γ : CtxDen Γ)
    (ρ : BoundDen β) (s : S) : Part (S × TyDen A) where
  Dom := ∃ p : S × TyDen A, Eval (ε := ε) h γ ρ s p.1 p.2
  get hd := Classical.choose hd

/-- Membership in the observation is exactly evaluation. -/
theorem mem_observe_iff {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) (γ : CtxDen Γ)
    (ρ : BoundDen β) (s : S) (p : S × TyDen A) :
    p ∈ observe (ε := ε) h γ ρ s ↔ Eval (ε := ε) h γ ρ s p.1 p.2 := by
  constructor
  · rintro ⟨hd, rfl⟩
    exact Classical.choose_spec hd
  · intro he
    refine ⟨⟨p, he⟩, ?_⟩
    obtain ⟨h₁, h₂⟩ :=
      Eval.deterministic (Classical.choose_spec (⟨p, he⟩ :
        ∃ q : S × TyDen A, Eval (ε := ε) h γ ρ s q.1 q.2)) he
    exact Prod.ext h₁ h₂

/-- An evaluation is observed. -/
theorem Eval.mem_observe {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} {h : HasType Φ Γ β t A} {γ : CtxDen Γ}
    {ρ : BoundDen β} {s s' : S} {v : TyDen A}
    (he : Eval (ε := ε) h γ ρ s s' v) : (s', v) ∈ observe (ε := ε) h γ ρ s :=
  (mem_observe_iff h γ ρ s (s', v)).2 he

/-- The observation is defined exactly when the program terminates. -/
theorem observe_dom_iff {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) (γ : CtxDen Γ)
    (ρ : BoundDen β) (s : S) :
    (observe (ε := ε) h γ ρ s).Dom ↔ ∃ s' v, Eval (ε := ε) h γ ρ s s' v :=
  ⟨fun ⟨p, hp⟩ ↦ ⟨p.1, p.2, hp⟩, fun ⟨s', v, hv⟩ ↦ ⟨(s', v), hv⟩⟩

/-- Divergence is exactly an undefined observation. -/
theorem observe_eq_none_iff {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) (γ : CtxDen Γ)
    (ρ : BoundDen β) (s : S) :
    observe (ε := ε) h γ ρ s = Part.none ↔ Diverges (ε := ε) h γ ρ s := by
  rw [Part.eq_none_iff]
  constructor
  · rintro hn ⟨s', v, hv⟩
    exact hn (s', v) (Eval.mem_observe hv)
  · intro hd p hp
    exact hd ⟨p.1, p.2, (mem_observe_iff h γ ρ s p).1 hp⟩

/-- Termination is exactly a defined observation. -/
theorem observe_eq_some_iff {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) (γ : CtxDen Γ)
    (ρ : BoundDen β) (s : S) (s' : S) (v : TyDen A) :
    observe (ε := ε) h γ ρ s = Part.some (s', v) ↔ Eval (ε := ε) h γ ρ s s' v := by
  rw [Part.eq_some_iff]
  exact mem_observe_iff h γ ρ s (s', v)

/-- The observation of a closed program, as a function of the initial state. -/
noncomputable def observeClosed {t : Tm Empty Φ 0} {A : τ}
    (h : HasType Φ (.nil : Ctx Empty τ) .nil t A) (s : S) : Part (S × TyDen A) :=
  observe (ε := ε) h PUnit.unit PUnit.unit s

/-- Two closed programs are *observationally indistinguishable* in a given
state model when they have the same observation from every state.  This is the
relation the completeness question is about: the equational theory is sound for
it (through the denotational semantics in `StateT S Part`), but not complete,
because a state model cannot see effects performed by a computation that never
returns. -/
def ModelObsEq {t₁ t₂ : Tm Empty Φ 0} {A : τ}
    (h₁ : HasType Φ (.nil : Ctx Empty τ) .nil t₁ A)
    (h₂ : HasType Φ (.nil : Ctx Empty τ) .nil t₂ A) : Prop :=
  ∀ s : S, observeClosed (ε := ε) h₁ s = observeClosed (ε := ε) h₂ s

/-! ## A divergence criterion for loops

The only way a `λ_iter` program can fail to return is by looping forever, so
the basic divergence lemma is about `iter`: a loop whose body never returns
`ι_l` never terminates.  This is what makes the pair of programs

```
loop  := iter () { ι_r x : ι_r x }
loopF := iter () { ι_r x : let _ = f x; ι_r x }
```

operationally indistinguishable in *every* state model, whatever `f` does. -/

/-- A loop body that never returns `ι_l` has no successful run. -/
theorem IterEval.not_of_never_inl {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {b : Tm ν Φ (n + 1)} {A B : τ}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β}
    (hbody : ∀ (y : TyDen A) (t t' : S) (w : TyDen (LambdaIter.coprod B A))
      (z : TyDen B), Eval (ε := ε) hb γ (ρ, y) t t' w →
      TypeModel.coprodEquiv B A w ≠ Sum.inl z) :
    {x : TyDen A} → {s s' : S} → {v : TyDen B} →
    IterEval (ε := ε) hb γ ρ x s s' v → False
  | _, _, _, _, .done hx hw => hbody _ _ _ _ _ hx hw
  | _, _, _, _, .more _ _ rest => IterEval.not_of_never_inl hbody rest

/-- A loop whose body never returns `ι_l` diverges from every state. -/
theorem Diverges.iter {Γ : Ctx ν τ} {n : Nat} {β : BoundCtx τ n}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    {ha : HasType Φ Γ β a A}
    {hb : HasType Φ Γ (.snoc β A) b (LambdaIter.coprod B A)}
    {γ : CtxDen Γ} {ρ : BoundDen β} (s : S)
    (hbody : ∀ (y : TyDen A) (t t' : S) (w : TyDen (LambdaIter.coprod B A))
      (z : TyDen B), Eval (ε := ε) hb γ (ρ, y) t t' w →
      TypeModel.coprodEquiv B A w ≠ Sum.inl z) :
    Diverges (ε := ε) (HasType.iter ha hb) γ ρ s := by
  rintro ⟨s', v, he⟩
  cases he with
  | iter _ hloop => exact IterEval.not_of_never_inl hbody hloop

end Isotope.LambdaIter.Opsem
