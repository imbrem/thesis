import Isotope.Elgot.Brookes.Iteration
import Mathlib.Logic.Function.Basic

/-!
# Sequential consistency as a standard Brookes model

The *standard* Brookes model takes traces over the alphabet `S × S` of
rely-guarantee pairs, and closes trace sets under Brookes's two rules:

* **stuttering** — `ε ↠ ⟨μ, μ⟩`: the program may do nothing;
* **mumbling** — `⟨μ, ρ⟩⟨ρ, θ⟩ ↠ ⟨μ, θ⟩`: the environment may do nothing.

Sequential consistency is this model with states `S := Loc → Val`.  The `write`
denotation is the paper's; `read` is not given in the paper, and the definition
here is the obvious dual — a read relies on some `μ`, guarantees `μ` unchanged,
and returns `μ ℓ`.  The stutter step `⟨μ, μ⟩` in `read` cannot be dropped: the
empty trace records nothing, so `{(ε, v) | ∃ μ, μ ℓ = v}` would return an
arbitrary value with no evidence of which state was relied upon.

This file also proves the two soundness invariants used to *separate*
computations, since refinement alone can only ever be exhibited by a witness:
no rewrite produces the empty trace, and every rewrite preserves membership of
all rely-guarantee pairs in a fixed preorder.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {S : Type u}

/-- Brookes's one-step closure rules: insert a stutter `⟨μ, μ⟩` anywhere in the
trace, or mumble two composable steps `⟨μ, ρ⟩⟨ρ, θ⟩` into `⟨μ, θ⟩`. -/
inductive Step (S : Type u) : Trace (S × S) → Trace (S × S) → Prop
  | stutter (μ : S) (t : Trace (S × S)) : Step S t ((μ, μ) :: t)
  | mumble (μ ρ θ : S) (t : Trace (S × S)) : Step S ((μ, ρ) :: (ρ, θ) :: t) ((μ, θ) :: t)
  | cons (p : S × S) {t t' : Trace (S × S)} : Step S t t' → Step S (p :: t) (p :: t')

theorem Step.appendRight {t t' : Trace (S × S)} (h : Step S t t') (u : Trace (S × S)) :
    Step S (t ++ u) (t' ++ u) := by
  induction h with
  | stutter μ t => exact Step.stutter μ (t ++ u)
  | mumble μ ρ θ t => exact Step.mumble μ ρ θ (t ++ u)
  | cons p _ ih => exact Step.cons p ih

/-- The sequential-consistency closure operator, presented by its generating
stuttering and mumbling rules. -/
def rewriting (S : Type u) : Rewriting (S × S) where
  Step := Step S
  step_cons := fun e {_ _} h ↦ Step.cons e h
  step_appendRight := fun {_ _} h u ↦ Step.appendRight h u

@[simp] theorem rewriting_Step (t t' : Trace (S × S)) :
    (rewriting S).Step t t' ↔ Step S t t' := Iff.rfl

/-- No rewrite ever produces the empty trace. -/
theorem Step.ne_nil {t t' : Trace (S × S)} (h : Step S t t') : t' ≠ [] := by
  cases h <;> exact List.cons_ne_nil _ _

/-- Consequently the empty trace refines to nothing but itself, and only the
empty trace refines to it. -/
theorem refines_nil {t : Trace (S × S)} (h : (rewriting S).Refines t []) : t = [] := by
  cases h with
  | refl => rfl
  | tail _ hs => exact absurd rfl (Step.ne_nil hs)

/-- Every rely-guarantee pair of a trace lies in the relation `r`. -/
def Compat (r : S → S → Prop) (t : Trace (S × S)) : Prop := ∀ p ∈ t, r p.1 p.2

/-- Stuttering and mumbling are sound for any preorder on states: a single
rewrite cannot leave the pairs of a trace outside a reflexive, transitive `r`. -/
theorem Step.compat {r : S → S → Prop} (hrefl : ∀ x, r x x)
    (htrans : ∀ x y z, r x y → r y z → r x z) {t t' : Trace (S × S)} (h : Step S t t') :
    Compat r t → Compat r t' := by
  induction h with
  | stutter μ t =>
    intro ht p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact hrefl μ
    · exact ht p hp
  | mumble μ ρ θ t =>
    intro ht p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact htrans μ ρ θ (ht (μ, ρ) (by simp)) (ht (ρ, θ) (by simp))
    · exact ht p (by simp [hp])
  | cons q _ ih =>
    intro ht p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact ht p (by simp)
    · exact ih (fun p' hp' ↦ ht p' (by simp [hp'])) p hp

/-- Refinement is sound for any preorder on states. -/
theorem refines_compat {r : S → S → Prop} (hrefl : ∀ x, r x x)
    (htrans : ∀ x y z, r x y → r y z → r x z) {t t' : Trace (S × S)}
    (h : (rewriting S).Refines t t') (ht : Compat r t) : Compat r t' := by
  induction h with
  | refl => exact ht
  | tail _ hs ih => exact Step.compat hrefl htrans hs ih

/-- A trace refined from the empty trace consists entirely of stutters. -/
theorem compat_eq_of_refines_nil {t : Trace (S × S)}
    (h : (rewriting S).Refines [] t) : ∀ p ∈ t, p.1 = p.2 :=
  refines_compat (r := Eq) (fun _ ↦ rfl) (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) h (by simp [Compat])

/-! ## Stores, reads and writes -/

variable {Loc Val : Type u}

/-- The sequential-consistency state: a map from locations to values. -/
abbrev Store (Loc Val : Type u) : Type u := Loc → Val

/-- The Brookes monad of sequentially consistent computations over `Loc`, `Val`. -/
abbrev Comp (Loc Val : Type u) (A : Type u) : Type u :=
  Brookes (rewriting (Store Loc Val)) A

/-- The paper's `write (ℓ, v) := c₁({⟨μ, [ℓ ↦ v]μ⟩ ⊢ () | μ ∈ S})`. -/
def write [DecidableEq Loc] (ℓ : Loc) (v : Val) : Comp Loc Val PUnit :=
  close _ {p | ∃ μ : Store Loc Val, p.1 = [(μ, Function.update μ ℓ v)]}

/-- A read relies on some state `μ`, guarantees it unchanged, and returns `μ ℓ`.
This denotation is not in the paper; it is the obvious dual of `write`. -/
def read (ℓ : Loc) : Comp Loc Val Val :=
  close _ {p | ∃ μ : Store Loc Val, p.1 = [(μ, μ)] ∧ p.2 = μ ℓ}

theorem mem_write_iff [DecidableEq Loc] (ℓ : Loc) (v : Val)
    (t : Trace (Store Loc Val × Store Loc Val)) (x : PUnit) : (t, x) ∈ write ℓ v ↔
      ∃ μ : Store Loc Val, (rewriting _).Refines [(μ, Function.update μ ℓ v)] t := by
  constructor
  · rintro ⟨t₀, ⟨μ, rfl⟩, hr⟩
    exact ⟨μ, hr⟩
  · rintro ⟨μ, hr⟩
    exact ⟨_, ⟨μ, rfl⟩, hr⟩

theorem mem_read_iff (ℓ : Loc) (t : Trace (Store Loc Val × Store Loc Val)) (x : Val) :
    (t, x) ∈ read ℓ ↔ ∃ μ : Store Loc Val, μ ℓ = x ∧ (rewriting _).Refines [(μ, μ)] t := by
  constructor
  · rintro ⟨t₀, ⟨μ, rfl, hx⟩, hr⟩
    exact ⟨μ, hx.symm, hr⟩
  · rintro ⟨μ, rfl, hr⟩
    exact ⟨_, ⟨μ, rfl, rfl⟩, hr⟩

theorem mem_write [DecidableEq Loc] (ℓ : Loc) (v : Val) (μ : Store Loc Val) :
    ([(μ, Function.update μ ℓ v)], PUnit.unit) ∈ write ℓ v :=
  (mem_write_iff ℓ v _ _).2 ⟨μ, .refl⟩

theorem mem_read (ℓ : Loc) (μ : Store Loc Val) : ([(μ, μ)], μ ℓ) ∈ read ℓ :=
  (mem_read_iff ℓ _ _).2 ⟨μ, rfl, .refl⟩

/-- Neither a read nor a write is the trivial computation: their traces are never
empty, whereas `pure` admits the empty trace. -/
theorem not_mem_read_nil (ℓ : Loc) (x : Val) : (([] : Trace _), x) ∉ read ℓ := by
  rintro h
  obtain ⟨μ, -, hr⟩ := (mem_read_iff ℓ [] x).1 h
  exact absurd (refines_nil hr) (by simp)

theorem read_ne_pure (ℓ : Loc) (v : Val) : read ℓ ≠ (pure v : Comp Loc Val Val) := by
  intro h
  exact not_mem_read_nil ℓ v (h ▸ Brookes.mem_pure (c := rewriting (Store Loc Val)) v)

theorem not_mem_write_nil [DecidableEq Loc] (ℓ : Loc) (v : Val) (x : PUnit) :
    (([] : Trace _), x) ∉ write ℓ v := by
  rintro h
  obtain ⟨μ, hr⟩ := (mem_write_iff ℓ v [] x).1 h
  exact absurd (refines_nil hr) (by simp)

theorem write_ne_pure [DecidableEq Loc] (ℓ : Loc) (v : Val) :
    write ℓ v ≠ (pure PUnit.unit : Comp Loc Val PUnit) := by
  intro h
  exact not_mem_write_nil ℓ v PUnit.unit
    (h ▸ Brookes.mem_pure (c := rewriting (Store Loc Val)) PUnit.unit)

end SeqCst

end Isotope.Elgot.Brookes
