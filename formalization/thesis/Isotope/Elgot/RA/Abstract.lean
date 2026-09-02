import Isotope.Elgot.RA.Examples

/-!
# The Abstract model `A`, and how far up the tower the unit laws reach

Dvir, Kammar and Lahav (`release-acquire`) close the tower of models with the
**Abstract model** (journal §7.5, p.35, verbatim):

> "Finally, we define the abstract model, `A` as the `𝔤𝔠𝔞`-monad structure,
> where `𝔞 ≜ {Ti, Ab, Di}` are closure rules presented below.  This model
> fulfills the basic requirement of a monadic model: **Proposition 7.8.** `A`
> is a monad."

The three rules are transcribed in `Isotope/Elgot/RA/Rewrite.lean`; this file is
about the model they generate.

## What is transcribed and what is ours

* `Abstract`, the carrier `Comp gcaRules`, is the paper's `A` (journal §7.2
  p.28 for the `★`-monad structure, §7.5 p.35 for `★ = 𝔤𝔠𝔞`), less
  countability — see boundary item 5 of `Isotope/Elgot/RA.lean`.
* **Proposition 7.8 is stated without proof** in both the journal version
  (p.35) and the ESOP full version (Proposition 6.7, p.31).  The paper's only
  supporting argument anywhere is Example 8.6 (journal p.41), which reduces
  *associativity* for `C` and `A` to Deferral of Closure (Lemma 8.5) plus
  associativity for `N`; neither unit law is argued for any model.  So
  everything proved below is **original work, not a port**.
* `gcTiAbRules = 𝔤𝔠 ∪ {Ti, Ab}` is **not a model of the paper**.  It is the
  fragment of `𝔤𝔠𝔞` for which we can prove the unit laws, and it exists here
  only to say exactly how far the argument of `Isotope/Elgot/RA/Monad.lean`
  reaches.

## The obstruction: `Di` creates local messages

Both unit laws for the Concrete model run on one invariant: a trace in the
closure of `return r` has no local messages (`closure_pureGen_own`), hence all
its transitions are stutters, hence it can be grown from `return`'s
one-transition trace by `St` and absorbed by `Rw`/`Fw`.

`Ti` and `Ab` preserve that invariant *vacuously*: both act at a transition
`⟨μ, ρ ⊎ {ν}⟩` with `ν ∉ μ`, so their source already has a local message.  This
is why `Refines.own_empty` holds at `gcTiAbRules` and both unit laws with it.

`Di` does **not**.  Its source `(α ξ⟨μ, ρ⊎{ν}⟩ η⊎{ν} ω)[↑ε]` constrains only
`ε` to be local (journal Fig. 14's caption, and the ESOP conference version's
Fig. 7: "while `ε` must be a local message, `ν` and `ν′` can appear anywhere in
the trace's sequence"), so `μ` may contain `ν` and the source may be a
stutter-only trace, while the target `α ξ⟨μ, ρ⊎{ν,ε}⟩ η⊎{ν,ε} ω` always has the
local message `ε`.  `dilute_return` below exhibits exactly that, out of the
paper's own initial memory, so this is not a defect of the transcription:

> `return_A r` contains traces with local messages; `return_C r` does not.

Consequently the paper's route to Proposition 7.8 must be the one it sketches
for associativity — Deferral of Closure (Lemma 8.5, journal p.41), whose
content at the bind seam is the `Ls ↔ Ti`, `Ex ↔ Ab`, `Cn ↔ Di` mirroring of
journal p.41: an `𝔞`-rewrite of one operand is matched by a `𝔤`-rewrite of the
*other* operand followed by an `𝔞`-rewrite of the seam.  That lemma is not
formalized here, and neither unit law for `A` is claimed.
-/

universe u

namespace Isotope.Elgot.RA

open Isotope.Elgot

variable {Loc Val : Type} {R R' : RuleSet} {A B : Type u}

/-! ## The carrier -/

/-- The **Abstract model** `A` (journal §7.5, p.35): the `𝔤𝔠𝔞`-monad structure,
i.e. `𝔤𝔠𝔞`-closed sets of traces. -/
abbrev Abstract (Loc Val : Type) (A : Type u) : Type u := Comp gcaRules Loc Val A

/-! ## The model tower, compared

The paper states the comparison in one clause (journal §8.2, p.41): "**Deferral
of Closure** also applies to `C` and `A` instead of `G`, since
`G X ⊆ C X ⊆ A X`."  Read literally that is false, and the paper gives no
argument: `G X`, `C X`, `A X` are the sets of `★`-closed sets of traces, and a
`𝔤`-closed set need not be `𝔤𝔠`-closed.  What is true, and what the sentence
must mean, is that the *closure operators* are ordered — `closure_le_closure`
below, which is `closure_mono_rules` — so that pointwise `⟦M⟧_G ⊆ ⟦M⟧_C ⊆ ⟦M⟧_A`;
the carriers are ordered the *other* way (`Closed.mono_rules`). -/

/-- Closedness is antitone in the rule set: an `A`-computation is in particular
a `C`-computation, and a `C`-computation a `G`-computation. -/
theorem Closed.mono_rules (hR : R ⊆ R') {U : Set (PreTrace Loc Val A)}
    (h : Closed R' U) : Closed R U := fun τ hτ π hstep ↦ h τ hτ π (hstep.mono hR)

/-- `⟦·⟧_G ⊆ ⟦·⟧_C ⊆ ⟦·⟧_A`, pointwise: enlarging the rule set enlarges every
denotation.  This is what the paper's `G X ⊆ C X ⊆ A X` (p.41) amounts to. -/
theorem closure_le_closure (hR : R ⊆ R') (S : Set (PreTrace Loc Val A)) :
    closure R S ⊆ closure R' S := closure_mono_rules hR S

namespace Comp

/-- Forgetting closure under the extra rules: `A X → C X → G X`. -/
def restrict (hR : R ⊆ R') (P : Comp R' Loc Val A) : Comp R Loc Val A where
  traces := P.traces
  isTrace := P.isTrace
  closed := P.closed.mono_rules hR

@[simp] theorem traces_restrict (hR : R ⊆ R') (P : Comp R' Loc Val A) :
    (restrict hR P).traces = P.traces := rfl

/-- Closing under the extra rules: `G X → C X → A X`.  At `R = 𝔤𝔠`,
`R' = 𝔤𝔠𝔞` this is the operator the paper writes `(·)𝔞` in Lemma 8.7
(Retroactive Closure, journal p.41). -/
def extend (R' : RuleSet) (P : Comp R Loc Val A) : Comp R' Loc Val A :=
  close R' P.traces P.isTrace

@[simp] theorem traces_extend (R' : RuleSet) (P : Comp R Loc Val A) :
    (extend R' P).traces = closure R' P.traces := rfl

theorem le_extend (P : Comp R Loc Val A) (hR : R ⊆ R') :
    P ≤ restrict hR (extend R' P) := subset_closure

theorem extend_restrict (hR : R ⊆ R') (Q : Comp R' Loc Val A) :
    extend R' (restrict hR Q) = Q :=
  ext (Q.closed.closure_eq)

/-- Closing under more rules is left adjoint to forgetting: the Abstract model
is a *reflective* sub-poset of the Concrete one. -/
theorem extend_le_iff (hR : R ⊆ R') (P : Comp R Loc Val A) (Q : Comp R' Loc Val A) :
    extend R' P ≤ Q ↔ P ≤ restrict hR Q :=
  ⟨fun h ↦ Set.Subset.trans subset_closure h,
    fun h ↦ closure_subset_of_closed Q.closed h⟩

end Comp

/-! ## The unit laws, for `𝔠 ⊆ ★ ⊆ 𝔤𝔠 ∪ {Ti, Ab}`

`Comp.left_neutrality` and `Comp.right_neutrality` are proved in
`Isotope/Elgot/RA/Monad.lean` for every `𝔠 ⊆ R ⊆ 𝔤𝔠 ∪ {Ti, Ab}`; the two
theorems below are the instances at the top of that range.  **Original work**:
the paper argues no unit law for any of its models. -/

/-- **Left Neutrality** for `𝔤𝔠 ∪ {Ti, Ab}`: the tighten–absorb fragment of the
Abstract model.  **Original work.** -/
theorem pure_bind_gcTiAb (r : A) (f : A → Comp gcTiAbRules Loc Val B) :
    (Pure.pure r : Comp gcTiAbRules Loc Val A) >>= f = f r :=
  Comp.left_neutrality cRules_subset_gcTiAbRules (subset_refl _) r f

/-- **Right Neutrality** for `𝔤𝔠 ∪ {Ti, Ab}`.  **Original work.** -/
theorem bind_pure_gcTiAb (P : Comp gcTiAbRules Loc Val A) : P >>= Pure.pure = P :=
  Comp.right_neutrality cRules_subset_gcTiAbRules (subset_refl _) P

/-! ## Iteration for the Abstract model

Everything in `Isotope/Elgot/RA/Iteration.lean` that does not need the monad
laws is uniform in the rule set, so the Abstract model has the iteration
operator and its fixpoint law for free; nothing about traces is re-proved.  The
remaining Elgot laws (`naturality`, `uniformity`, `codiagonal`) are proved there
under the single hypothesis `LawfulMonad (Comp R Loc Val)`, and `codiagonal` in
particular is proved order-theoretically, from `bind_mono`, `bot_bind`,
`iUnion_bind`, `bind_iUnion` and `fixpoint` alone.  So they transfer to `A` the
moment associativity does — which, for `A` as for `C`, is open here. -/

/-- The Abstract model's iteration operator satisfies the fixpoint law. -/
theorem Abstract.iterate_fixpoint (f : A → Abstract Loc Val (B ⊕ A)) :
    Comp.iterate f = fun a ↦ f a >>= Sum.elim Pure.pure (Comp.iterate f) :=
  Comp.fixpoint f

/-- Two messages agreeing on all four data fields are equal. -/
theorem Msg.ext_fields {ν ε : Msg Loc Val} (hlc : ν.lc = ε.lc) (hvl : ν.vl = ε.vl)
    (hi : ν.i = ε.i) (hvw : ν.vw = ε.vw) : ν = ε := by
  cases ν; cases ε; simp_all

/-! ## Flat memories

A memory with one message per location, all sharing a view `κ` and an initial
timestamp `q`.  The paper's initial memory (journal §6.1) is the case
`κ = λ_. t`, `q = t - 1`; we need the general case because *pulling* the initial
memory along a message moves the shared view at one location.  This definition
is ours. -/

/-- One message per location, all with value `v`, initial timestamp `q` and
carried view `κ`. -/
def flatMsg (v : Val) (q : ℚ) (κ : View Loc) (h : ∀ ℓ, q < κ ℓ) (ℓ : Loc) :
    Msg Loc Val where
  lc := ℓ
  vl := v
  i := q
  vw := κ
  lt := h ℓ

@[simp] theorem flatMsg_lc (v : Val) (q : ℚ) (κ : View Loc) (h : ∀ ℓ, q < κ ℓ) (ℓ : Loc) :
    (flatMsg (Val := Val) v q κ h ℓ).lc = ℓ := rfl

@[simp] theorem flatMsg_vl (v : Val) (q : ℚ) (κ : View Loc) (h : ∀ ℓ, q < κ ℓ) (ℓ : Loc) :
    (flatMsg (Val := Val) v q κ h ℓ).vl = v := rfl

@[simp] theorem flatMsg_i (v : Val) (q : ℚ) (κ : View Loc) (h : ∀ ℓ, q < κ ℓ) (ℓ : Loc) :
    (flatMsg (Val := Val) v q κ h ℓ).i = q := rfl

@[simp] theorem flatMsg_vw (v : Val) (q : ℚ) (κ : View Loc) (h : ∀ ℓ, q < κ ℓ) (ℓ : Loc) :
    (flatMsg (Val := Val) v q κ h ℓ).vw = κ := rfl

@[simp] theorem flatMsg_t (v : Val) (q : ℚ) (κ : View Loc) (h : ∀ ℓ, q < κ ℓ) (ℓ : Loc) :
    (flatMsg (Val := Val) v q κ h ℓ).t = κ ℓ := rfl

/-- The memory of all the `flatMsg`s. -/
def flatMem (v : Val) (q : ℚ) (κ : View Loc) (h : ∀ ℓ, q < κ ℓ) : Memory Loc Val :=
  Set.range (flatMsg v q κ h)

@[simp] theorem mem_flatMem_iff {v : Val} {q : ℚ} {κ : View Loc} {h : ∀ ℓ, q < κ ℓ}
    {ν : Msg Loc Val} : ν ∈ flatMem v q κ h ↔ ν = flatMsg v q κ h ν.lc := by
  constructor
  · rintro ⟨ℓ, rfl⟩; rfl
  · intro hν; exact ⟨ν.lc, hν.symm⟩

theorem flatMsg_mem (v : Val) (q : ℚ) (κ : View Loc) (h : ∀ ℓ, q < κ ℓ) (ℓ : Loc) :
    flatMsg v q κ h ℓ ∈ flatMem (Val := Val) v q κ h := ⟨ℓ, rfl⟩

/-- The shared view points downwards into a flat memory. -/
theorem pointsDownInto_flatMem (v : Val) (q : ℚ) (κ : View Loc) (h : ∀ ℓ, q < κ ℓ) :
    PointsDownInto κ (flatMem (Val := Val) v q κ h) :=
  fun ℓ ↦ ⟨flatMsg v q κ h ℓ, ⟨ℓ, rfl⟩, rfl, rfl, le_refl _⟩

theorem flatMem_wellFormed [Finite Loc] [Nonempty Loc] (v : Val) (q : ℚ) (κ : View Loc)
    (h : ∀ ℓ, q < κ ℓ) : WellFormed (flatMem (Val := Val) v q κ h) where
  finite := Set.finite_range _
  nonempty := ⟨_, flatMsg_mem v q κ h (Classical.arbitrary Loc)⟩
  causal := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rintro ν hν ε hε hlc -
      rw [mem_flatMem_iff] at hν hε
      rw [hν, hε, hlc]
    · rintro ν hν ℓ
      refine ⟨flatMsg v q κ h ℓ, ⟨ℓ, rfl⟩, rfl, ?_⟩
      rw [mem_flatMem_iff] at hν
      change ν.vw ℓ = κ ℓ
      rw [hν]; rfl
    · rintro ν hν ℓ
      refine ⟨flatMsg v q κ h ℓ, ⟨ℓ, rfl⟩, rfl, ?_, ?_⟩
      · rw [mem_flatMem_iff] at hν
        change ν.vw ℓ = κ ℓ
        rw [hν]; rfl
      · rw [mem_flatMem_iff] at hν
        change κ ≤ ν.vw
        rw [hν]; exact le_refl _
  cycles := by
    rintro ν hν -
    refine ⟨hν, ?_⟩
    rintro ε hε hlc
    rw [mem_flatMem_iff] at hν hε
    rw [hν, hε, hlc]

/-- The paper's initial memory is the flat memory with the constant view. -/
theorem initialMem_eq_flatMem (v : Val) (t : ℚ) :
    initialMem (Loc := Loc) v t = flatMem v (t - 1) (fun _ ↦ t) (fun _ ↦ by simp) := rfl

/-! ## `Dilute` applied to `return`

Everything below is **ours**: the paper exhibits no `Di`-rewrite anywhere, and
asserts the separation between the models only in prose ("the denotational
semantics follows the operational semantics too closely.  It is insufficiently
abstract, invalidating some program transformations", journal p.26).

We `Di`-rewrite a trace of `return r` built on the paper's own initial memory.
Take `ν` the initial message at `ℓ` and `ε` the message that dovetails after it
with the same value `v₀`, so `ν ⤙= ε`; then

* the target is `α ⟨μ, μ ⊎ {ε}⟩ ω ◁ r` with `μ` the initial memory: a trace,
  with the **local** message `ε`;
* the source is that pre-trace pulled along `ε`, which — because pulling merges
  `ν` and `ε` into one message — is the *stutter* trace
  `κ ⟨μ[↑ε], μ[↑ε]⟩ κ ◁ r`, i.e. literally an element of `return r`.

So `Di` manufactures a local message out of a trace that has none, which no
rule of `𝔤𝔠 ∪ {Ti, Ab}` can do (`Refines.own_empty`). -/

section Dilute

variable [DecidableEq Loc]

/-- The view carried by the message `Dilute` introduces: the constant view
advanced at `ℓ`. -/
def dilView (t₀ : ℚ) (ℓ : Loc) : View Loc := setView (fun _ ↦ t₀) ℓ (t₀ + 1)

theorem sub_one_lt_dilView (t₀ : ℚ) (ℓ ℓ' : Loc) : t₀ - 1 < dilView t₀ ℓ ℓ' := by
  by_cases h : ℓ' = ℓ
  · subst h; rw [dilView, setView_self]; linarith
  · rw [dilView, setView_of_ne _ h]; linarith

@[simp] theorem dilView_self (t₀ : ℚ) (ℓ : Loc) : dilView t₀ ℓ ℓ = t₀ + 1 :=
  setView_self ..

theorem dilView_of_ne {t₀ : ℚ} {ℓ ℓ' : Loc} (h : ℓ' ≠ ℓ) : dilView t₀ ℓ ℓ' = t₀ :=
  setView_of_ne _ h

theorem storedMsg_vw_eq_dilView (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (storedMsg (Loc := Loc) (Val := Val) t₀ ℓ v).vw = dilView t₀ ℓ := rfl

/-- Pulling the constant view along `ε` advances it at `ℓ`. -/
theorem pull_const_view (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) :
    View.pull (storedMsg (Loc := Loc) (Val := Val) t₀ ℓ v₀) (fun _ ↦ t₀) = dilView t₀ ℓ := by
  funext ℓ'
  by_cases h : ℓ' = ℓ
  · subst h; simp [View.pull, dilView]
  · simp [View.pull, dilView, h]

/-- …and pulling the advanced view again does nothing. -/
theorem pull_dilView (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) :
    View.pull (storedMsg (Loc := Loc) (Val := Val) t₀ ℓ v₀) (dilView t₀ ℓ) = dilView t₀ ℓ := by
  refine View.pull_eq_self ?_
  simp only [storedMsg_lc, storedMsg_i, dilView_self]
  linarith

/-- Pulling the initial memory along `ε` gives a flat memory: every message
keeps its segment except the one at `ℓ`, which is stretched to cover `ε`. -/
theorem pull_initialMem (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) :
    Memory.pull (storedMsg (Loc := Loc) t₀ ℓ v₀) (initialMem (Loc := Loc) v₀ t₀)
      = flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ) := by
  have key : ∀ ℓ' : Loc, Msg.pull (storedMsg t₀ ℓ v₀) (initialMsg (Val := Val) v₀ t₀ ℓ')
      = flatMsg v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ) ℓ' := by
    intro ℓ'
    refine Msg.ext_fields rfl rfl rfl ?_
    rw [Msg.pull_vw, initialMsg_vw, flatMsg_vw, pull_const_view]
  ext ν
  constructor
  · rintro ⟨ϑ, hϑ, rfl⟩
    rw [mem_initialMem_iff] at hϑ
    rw [hϑ, key]
    exact flatMsg_mem _ _ _ _ _
  · intro hν
    rw [mem_flatMem_iff] at hν
    exact ⟨initialMsg v₀ t₀ ν.lc, ⟨ν.lc, rfl⟩, by rw [key, ← hν]⟩

variable [Finite Loc] [Nonempty Loc]

/-- **`Dilute` rewrites a trace of `return r` into one with a local message.**
The source is the initial memory pulled along `ε`, which is a `return`-trace;
the target has the local message `ε = ℓ:v₀@(t₀, t₀+1]⟪·⟫`.  **Original work**:
the paper gives no example of any `𝔞`-rewrite. -/
theorem dilute_return (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    TStep gcaRules
      (⟨dilView t₀ ℓ,
        Chro.single ⟨flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ),
          flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ)⟩,
        dilView t₀ ℓ, r⟩ : PreTrace Loc Val A)
      ⟨fun _ ↦ t₀, Chro.single ⟨initialMem v₀ t₀, storedMem v₀ t₀ ℓ v₀⟩, dilView t₀ ℓ, r⟩ := by
  set ν : Msg Loc Val := initialMsg v₀ t₀ ℓ with hνdef
  set ε : Msg Loc Val := storedMsg t₀ ℓ v₀ with hεdef
  set μ : Memory Loc Val := initialMem v₀ t₀ with hμdef
  have hνμ : ν ∈ μ := ⟨ℓ, rfl⟩
  have hεμ : ε ∉ μ := storedMsg_not_mem_initialMem v₀ t₀ ℓ v₀
  have hins : insert ν (μ \ {ν}) = μ := by
    rw [Set.insert_diff_singleton, Set.insert_eq_self.mpr hνμ]
  have hins2 : insert ν (insert ε (μ \ {ν})) = storedMem v₀ t₀ ℓ v₀ := by
    rw [Set.insert_comm, hins]
    rfl
  have hle : (fun _ ↦ t₀ : View Loc) ≤ dilView t₀ ℓ := by
    rw [dilView]; exact le_setView (by simp)
  have hde : Msg.DovetailEq ν ε := by
    refine ⟨⟨rfl, ?_, ?_⟩, rfl⟩
    · rw [hνdef, hεdef, initialMsg_t, storedMsg_i]
    · rw [hνdef, hεdef, initialMsg_vw, storedMsg_vw_eq_dilView]; exact hle
  refine ⟨?_, ?_⟩
  · have hsrc : (⟨dilView t₀ ℓ,
        Chro.single ⟨flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ),
          flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ)⟩,
        dilView t₀ ℓ, r⟩ : PreTrace Loc Val A)
        = ⟨View.pull ε (fun _ ↦ t₀),
            Chro.single ⟨flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ),
              flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ)⟩,
            View.pull ε (dilView t₀ ℓ), r⟩ := by
      rw [pull_const_view, pull_dilView]
    rw [hsrc]
    refine Step.dilute (by simp) [] [] μ (μ \ {ν}) ν ε hde hεμ (fun h ↦ hεμ h.1)
      (fun h ↦ h.2 rfl) (by simp [listFree]) (by simp [listFree]) ?_ ?_
    · simp only [Chro.single_toList, List.nil_append, List.map_nil, List.map_cons,
        List.map_nil]
      rw [hins]
      simp only [Transition.pull, List.cons.injEq, and_true, Transition.mk.injEq]
      exact ⟨(pull_initialMem v₀ t₀ ℓ).symm, (pull_initialMem v₀ t₀ ℓ).symm⟩
    · simp only [Chro.single_toList, List.nil_append, List.map_nil]
      rw [hins2]
  · refine ⟨?_, ?_, hle, ?_, ?_⟩
    · intro T hT
      simp only [Chro.single_toList, List.mem_singleton] at hT
      subst hT
      exact ⟨initialMem_wellFormed v₀ t₀, storedMem_wellFormed v₀ t₀ ℓ v₀,
        initialMem_subset_storedMem v₀ t₀ ℓ v₀⟩
    · exact pointsDownInto_initialMem v₀ t₀
    · intro ℓ'
      by_cases hl : ℓ' = ℓ
      · subst hl
        refine ⟨ε, storedMsg_mem v₀ t₀ ℓ' v₀, rfl, ?_, le_refl _⟩
        change dilView t₀ ℓ' (storedMsg t₀ ℓ' v₀).lc = (storedMsg t₀ ℓ' v₀).t
        rw [storedMsg_lc, storedMsg_t, dilView_self]
      · refine ⟨initialMsg v₀ t₀ ℓ', Set.mem_insert_of_mem _ ⟨ℓ', rfl⟩, rfl, ?_, ?_⟩
        · change dilView t₀ ℓ ℓ' = t₀
          exact dilView_of_ne hl
        · exact hle
    · intro ϑ hϑ
      simp only [Chro.single_own, Transition.own, hμdef, storedMem, Set.mem_diff,
        Set.mem_insert_iff] at hϑ
      obtain ⟨hϑ1 | hϑ1, hϑ2⟩ := hϑ
      · subst hϑ1
        refine ⟨?_, le_refl _, ?_⟩
        · rw [storedMsg_vw_eq_dilView]; exact hle
        · simp
      · exact absurd hϑ1 hϑ2

omit [Finite Loc] [Nonempty Loc] in
/-- The target of `dilute_return` has a local message. -/
theorem dilute_return_own (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    (⟨fun _ ↦ t₀, Chro.single ⟨initialMem v₀ t₀, storedMem v₀ t₀ ℓ v₀⟩, dilView t₀ ℓ, r⟩ :
      PreTrace Loc Val A).ch.own ≠ ∅ := by
  intro h
  rw [Chro.single_own] at h
  have hmem : storedMsg t₀ ℓ v₀ ∈
      (⟨initialMem v₀ t₀, storedMem v₀ t₀ ℓ v₀⟩ : Transition Loc Val).own :=
    ⟨Set.mem_insert _ _, storedMsg_not_mem_initialMem v₀ t₀ ℓ v₀⟩
  rw [h] at hmem
  exact hmem

/-- The source of `dilute_return` is a trace of `return r`. -/
theorem dilute_return_src_mem (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    (⟨dilView t₀ ℓ,
      Chro.single ⟨flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ),
        flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ)⟩,
      dilView t₀ ℓ, r⟩ : PreTrace Loc Val A) ∈ pureGen r :=
  ⟨_, _, flatMem_wellFormed _ _ _ _, pointsDownInto_flatMem _ _ _ _, rfl⟩

omit [Finite Loc] [Nonempty Loc] in
/-- …and it has no local messages. -/
theorem dilute_return_src_own (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    (⟨dilView t₀ ℓ,
      Chro.single ⟨flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ),
        flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ)⟩,
      dilView t₀ ℓ, r⟩ : PreTrace Loc Val A).ch.own = ∅ := by
  simp [Transition.own]

/-- The target of `dilute_return` is a trace of `return r` in the **Abstract**
model. -/
theorem dilute_return_mem_pure (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    (⟨fun _ ↦ t₀, Chro.single ⟨initialMem v₀ t₀, storedMem v₀ t₀ ℓ v₀⟩, dilView t₀ ℓ, r⟩ :
      PreTrace Loc Val A) ∈ (Pure.pure r : Abstract Loc Val A).traces :=
  ⟨_, dilute_return_src_mem v₀ t₀ ℓ r, Refines.single (dilute_return v₀ t₀ ℓ r)⟩

/-! ## The separation

`Di` is not derivable, and the Abstract model is strictly larger than the
Concrete one already at `return`.  **Original work**: the paper asserts that the
Concrete model is "insufficiently abstract" (journal p.26) but exhibits no trace
separating the two models and no transformation that `C` refutes. -/

omit [Finite Loc] [Nonempty Loc] in
/-- **No `𝔤𝔠 ∪ {Ti, Ab}`-rewriting sequence realises the `Di`-step**, since
having no local messages is invariant under those rules and `Di` creates one. -/
theorem not_refines_dilute_return (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    ¬ Refines gcTiAbRules
      (⟨dilView t₀ ℓ,
        Chro.single ⟨flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ),
          flatMem v₀ (t₀ - 1) (dilView t₀ ℓ) (sub_one_lt_dilView t₀ ℓ)⟩,
        dilView t₀ ℓ, r⟩ : PreTrace Loc Val A)
      ⟨fun _ ↦ t₀, Chro.single ⟨initialMem v₀ t₀, storedMem v₀ t₀ ℓ v₀⟩, dilView t₀ ℓ, r⟩ :=
  fun h ↦ dilute_return_own v₀ t₀ ℓ r
    (h.own_empty (subset_refl _) (dilute_return_src_own v₀ t₀ ℓ r))

set_option linter.unusedDecidableInType false in
/-- **`return_C r ⊊ return_A r`**: the unit of the Abstract model strictly
contains the unit of the Concrete model.  So the `𝔞` rules genuinely enlarge
every denotation, already at `return`, and `A` makes strictly fewer distinctions
between trace sets than `C` does. -/
theorem pure_concrete_ssubset_pure_abstract (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    (Pure.pure r : Comp gcRules Loc Val A).traces ⊂
      (Pure.pure r : Abstract Loc Val A).traces := by
  refine ⟨closure_le_closure gcRules_subset_gcaRules _, fun hsub ↦ ?_⟩
  exact dilute_return_own v₀ t₀ ℓ r
    (closure_pureGen_own gcRules_subset_gcTiAbRules r
      (hsub (dilute_return_mem_pure v₀ t₀ ℓ r)))

set_option linter.unusedDecidableInType false in
/-- The same separation against the whole tighten–absorb fragment: even with
`Ti` and `Ab`, `return` has no local messages, so it is `Di` alone that
enlarges it. -/
theorem pure_gcTiAb_ssubset_pure_abstract (v₀ : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    (Pure.pure r : Comp gcTiAbRules Loc Val A).traces ⊂
      (Pure.pure r : Abstract Loc Val A).traces := by
  refine ⟨closure_le_closure gcTiAbRules_subset_gcaRules _, fun hsub ↦ ?_⟩
  exact dilute_return_own v₀ t₀ ℓ r
    (closure_pureGen_own (subset_refl _) r (hsub (dilute_return_mem_pure v₀ t₀ ℓ r)))

end Dilute

end Isotope.Elgot.RA
