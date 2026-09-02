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

`Ti` and `Ab` are exercised positively at the end of this file — by
`absorb_two_writes`, which carries out the paper's `ℓ ≔ w ; ℓ ≔ v ↠ ℓ ≔ v` step
(journal p.37) on a concrete trace, and by `tighten_write`, which advances the
view of a local write to point at a later message at another location, the shape
of the paper's `Ti` step for write–read reordering (journal §E.5, p.59).
Without them nothing here would distinguish a faithful transcription of those
two rules from an over-constrained one, since their `own_empty` cases are
vacuous.

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

/-- Closing under the smaller rule set first changes nothing.

⚠ This is *not* the paper's **Retroactive Closure** (Lemma 8.7, journal p.41),
which states `⟦M⟧_A = ⟦M⟧_C^𝔞` for a *program* `M`: there the outer closure is
under `𝔞` **alone**, and the proof needs Rewrite Castling (Lemma 8.3) to move
the `𝔤𝔠`-rewrites in front of the `𝔞`-rewrites.  Here the outer closure is again
under the full `𝔤𝔠𝔞`, which makes the statement a triviality. -/
theorem closure_closure_of_subset (hR : R ⊆ R') (S : Set (PreTrace Loc Val A)) :
    closure R' (closure R S) = closure R' S :=
  Set.Subset.antisymm
    (closure_subset_of_closed (closure_closed R' S) (closure_le_closure hR S))
    (closure_mono subset_closure)

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

theorem extend_mono {P Q : Comp R Loc Val A} (h : P ≤ Q) :
    extend R' P ≤ extend R' Q := closure_mono h

/-- The reflector preserves `return`: `(return_C r)𝔞 = return_A r`. -/
theorem extend_pure (hR : R ⊆ R') (r : A) :
    extend R' (Pure.pure r : Comp R Loc Val A) = (Pure.pure r : Comp R' Loc Val A) :=
  ext (closure_closure_of_subset hR _)

/-- The reflector is **lax** monoidal for `>>=`.  Equality here is exactly the
paper's Deferral of Closure (Lemma 8.5, journal p.41) — `(P★ >>=_G f★)★ =
(P >>=_G f)★` for `𝔠 ⊆ ★ ⊆ 𝔠𝔞` — which is not formalized, so only this
inequality is available. -/
theorem extend_bind_le (hR : R ⊆ R') (P : Comp R Loc Val A) (f : A → Comp R Loc Val B) :
    extend R' (P >>= f) ≤ (extend R' P >>= fun a ↦ extend R' (f a)) := by
  change closure R' (closure R (bindGen P.traces (fun a ↦ (f a).traces))) ⊆
    closure R' (bindGen (closure R' P.traces) (fun a ↦ closure R' (f a).traces))
  rw [closure_closure_of_subset hR]
  exact closure_mono (bindGen_mono subset_closure (fun _ ↦ subset_closure))

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

/-! ## `Absorb` applied to two dovetailing writes

The paper's own worked example for `Ab` (journal p.37): *"The transformation
`ℓ ≔ w ; ℓ ≔ v ↠ ℓ ≔ v` is a concrete example where this rule is useful… Pick a
timestamp `t` from the interior of `β.seg`, a trace `π ∈ ⟦ℓ≔w⟧` with local
message that has the segment `(β.i, t]` and a trace `ϱ ∈ ⟦ℓ≔v⟧` with local
message that has the segment `(t, β.t]`.  After binding … use mumble to combine
the transitions, then absorb to replace these two messages with `β`."*

We build the memory that results from that mumble — the initial memory with two
dovetailing local writes at `ℓ` — and absorb them.  This is the first place in
the development where a `𝔞`-rule other than `Di` is *applied*, so it is also the
check that the side conditions we read into `ChroStep.absorb` are jointly
satisfiable on a genuine trace.  **Original work**: the paper gives the example
in prose and constructs no trace.
-/

section Absorb

variable [DecidableEq Loc]

/-- The upper of the two dovetailing writes at `ℓ`: `ℓ:v@(t₀+1, t₀+2]`.  The
lower one is `storedMsg t₀ ℓ w = ℓ:w@(t₀, t₀+1]`. -/
def absMsg (t₀ : ℚ) (ℓ : Loc) (v : Val) : Msg Loc Val :=
  writeMsg ℓ v (t₀ + 1) (t₀ + 2) (fun _ ↦ t₀) (by linarith)

@[simp] theorem absMsg_lc (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (absMsg (Val := Val) t₀ ℓ v).lc = ℓ := rfl

@[simp] theorem absMsg_vl (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (absMsg (Loc := Loc) t₀ ℓ v).vl = v := rfl

@[simp] theorem absMsg_i (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (absMsg (Loc := Loc) t₀ ℓ v).i = t₀ + 1 := rfl

@[simp] theorem absMsg_vw (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (absMsg (Loc := Loc) t₀ ℓ v).vw = setView (fun _ ↦ t₀) ℓ (t₀ + 2) := rfl

@[simp] theorem absMsg_t (t₀ : ℚ) (ℓ : Loc) (v : Val) :
    (absMsg (Loc := Loc) t₀ ℓ v).t = t₀ + 2 := by simp [absMsg]

/-- The two writes dovetail: `ℓ:w@(t₀,t₀+1] ⤙ ℓ:v@(t₀+1,t₀+2]`. -/
theorem absMsg_dovetail (t₀ : ℚ) (ℓ : Loc) (w v : Val) :
    Msg.Dovetail (storedMsg (Loc := Loc) t₀ ℓ w) (absMsg t₀ ℓ v) := by
  refine ⟨rfl, by simp, ?_⟩
  intro ℓ'
  by_cases h : ℓ' = ℓ
  · subst h; simp
  · simp [setView_of_ne _ h]

/-- The absorbed message `ε[i↦ν.i] = ℓ:v@(t₀, t₀+2]`, covering both segments. -/
theorem absMsg_setI (t₀ : ℚ) (ℓ : Loc) (w v : Val) :
    (absMsg t₀ ℓ v).setI (storedMsg (Loc := Loc) t₀ ℓ w).i (absMsg_dovetail t₀ ℓ w v).i_lt_t
      = writeMsg ℓ v t₀ (t₀ + 2) (fun _ ↦ t₀) (by linarith) :=
  Msg.ext_fields rfl rfl rfl rfl

theorem writeMsg_not_mem_initialMem (v₀ v : Val) (t₀ q t : ℚ) (ℓ : Loc) (κ : View Loc)
    (h : q < t) (hq : t₀ - 1 < q) :
    writeMsg ℓ v q t κ h ∉ initialMem (Loc := Loc) v₀ t₀ := by
  intro hmem
  rw [mem_initialMem_iff] at hmem
  have hi := congrArg Msg.i hmem
  simp only [writeMsg_i, initialMsg_i] at hi
  linarith

/-- The initial view is below the view carried by a write over it. -/
theorem initialView_le_writeMsg_vw (t₀ q t : ℚ) (ℓ : Loc) (v : Val) (h : q < t)
    (ht : t₀ ≤ t) : (fun _ ↦ t₀ : View Loc) ≤ (writeMsg ℓ v q t (fun _ ↦ t₀) h).vw := by
  rw [writeMsg_vw]; exact le_setView ht

variable [Finite Loc] [Nonempty Loc]

/-- The initial memory extended by a set `S` of extra writes is well formed, as
soon as: every extra message starts at or above `t₀`; extra messages at one
location do not overlap; every extra message carries a common view `κ` advanced
at its own location to its own final timestamp; `κ` points downwards into the
result; and at most one extra message is pointed at by `κ`.

This generalizes `storedMem_wellFormed` (the case `S = {ℓ:v@(t₀,t₀+1]}`,
`κ = λ_. t₀`) and is what the `𝔞` examples below need.  The last two hypotheses
are the ones that keep the paper's *cycle* condition true: an extra message can
only be pointed at through `κ`, so if two of them were, they would point at each
other and form a cycle of non-minimal messages. -/
theorem union_initialMem_wellFormed (v₀ : Val) (t₀ : ℚ) (κ : View Loc)
    (S : Memory Loc Val) (hfin : S.Finite)
    (hlo : ∀ χ ∈ S, t₀ ≤ χ.i)
    (hvw : ∀ χ ∈ S, χ.vw = setView κ χ.lc χ.t)
    (hκle : ∀ χ ∈ S, κ χ.lc ≤ χ.t)
    (hκpt : PointsDownInto κ (S ∪ initialMem (Loc := Loc) v₀ t₀))
    (hsc : ∀ χ ∈ S, ∀ χ' ∈ S, χ.lc = χ'.lc → (χ.seg ∩ χ'.seg).Nonempty → χ = χ')
    (hone : ∀ χ ∈ S, ∀ χ' ∈ S, κ χ.lc = χ.t → κ χ'.lc = χ'.t → χ = χ') :
    WellFormed (S ∪ initialMem (Loc := Loc) v₀ t₀) := by
  have hlt : ∀ χ ∈ S, t₀ < χ.t := fun χ hχ ↦ lt_of_le_of_lt (hlo χ hχ) χ.i_lt_t
  have hκvw : ∀ χ ∈ S, κ ≤ χ.vw := by
    intro χ hχ
    rw [hvw χ hχ]
    exact le_setView (hκle χ hχ)
  -- an extra message and an initial one never share a location and a segment
  have hsplit : ∀ χ ∈ S, ∀ ℓ' : Loc,
      (χ.seg ∩ (initialMsg (Val := Val) v₀ t₀ ℓ').seg).Nonempty → False := by
    rintro χ hχ ℓ' ⟨x, hx1, hx2⟩
    simp only [Msg.seg, initialMsg_t, initialMsg_i, Set.mem_Ioc] at hx2
    simp only [Msg.seg, Set.mem_Ioc] at hx1
    have := hlo χ hχ
    linarith [hx1.1, hx2.2]
  -- the view of an extra message reads `χ.t` at `χ.lc` and `κ` elsewhere
  have hvw_self : ∀ χ ∈ S, χ.vw χ.lc = χ.t := by
    intro χ hχ; rw [hvw χ hχ, setView_self]
  have hvw_ne : ∀ χ ∈ S, ∀ ℓ' : Loc, ℓ' ≠ χ.lc → χ.vw ℓ' = κ ℓ' := by
    intro χ hχ ℓ' h; rw [hvw χ hχ, setView_of_ne _ h]
  -- an extra message can only be pointed at through `κ`
  have hin : ∀ χ ∈ S, ∀ b ∈ S ∪ initialMem (Loc := Loc) v₀ t₀, b ≠ χ →
      PointsTo b.vw χ → κ χ.lc = χ.t := by
    rintro χ hχ b (hb | hb) hne hpt
    · by_cases hlc : χ.lc = b.lc
      · exact absurd (hsc b hb χ hχ hlc.symm ⟨χ.t, by
          rw [PointsTo, hvw b hb, hlc, setView_self] at hpt
          exact hpt ▸ b.t_mem_seg, χ.t_mem_seg⟩) hne
      · rw [PointsTo, hvw_ne b hb χ.lc hlc] at hpt
        exact hpt
    · rw [mem_initialMem_iff] at hb
      rw [PointsTo, hb] at hpt
      exact absurd hpt.symm (ne_of_gt (hlt χ hχ))
  refine ⟨hfin.union (Set.finite_range _), ⟨_, Or.inr ⟨Classical.arbitrary Loc, rfl⟩⟩,
    ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · -- scattered
    rintro χ (hχ | hχ) χ' (hχ' | hχ') hlceq hov
    · exact hsc χ hχ χ' hχ' hlceq hov
    · rw [mem_initialMem_iff] at hχ'
      exact absurd (hχ' ▸ hov) (fun h ↦ hsplit χ hχ χ'.lc h)
    · rw [mem_initialMem_iff] at hχ
      refine absurd ?_ (fun h ↦ hsplit χ' hχ' χ.lc h)
      obtain ⟨x, hx1, hx2⟩ := hov
      exact ⟨x, hx2, hχ ▸ hx1⟩
    · rw [mem_initialMem_iff] at hχ hχ'
      rw [hχ, hχ', hlceq]
  · -- connected
    rintro χ hχ ℓ''
    rcases hχ with hχ | hχ
    · by_cases hl : ℓ'' = χ.lc
      · subst hl
        exact ⟨χ, Or.inl hχ, rfl, hvw_self χ hχ⟩
      · obtain ⟨χ', hχ', hlc', hpt', -⟩ := hκpt ℓ''
        refine ⟨χ', hχ', hlc', ?_⟩
        rw [PointsTo, hlc', hvw_ne χ hχ ℓ'' hl, ← hlc']
        exact hpt'
    · rw [mem_initialMem_iff] at hχ
      refine ⟨initialMsg v₀ t₀ ℓ'', Or.inr ⟨ℓ'', rfl⟩, rfl, ?_⟩
      change χ.vw ℓ'' = t₀
      rw [hχ]; rfl
  · -- causally connected
    rintro χ hχ ℓ''
    rcases hχ with hχ | hχ
    · by_cases hl : ℓ'' = χ.lc
      · subst hl
        exact ⟨χ, Or.inl hχ, rfl, hvw_self χ hχ, le_refl _⟩
      · obtain ⟨χ', hχ', hlc', hpt', hle'⟩ := hκpt ℓ''
        refine ⟨χ', hχ', hlc', ?_, le_trans hle' (hκvw χ hχ)⟩
        rw [PointsTo, hlc', hvw_ne χ hχ ℓ'' hl, ← hlc']
        exact hpt'
    · rw [mem_initialMem_iff] at hχ
      refine ⟨initialMsg v₀ t₀ ℓ'', Or.inr ⟨ℓ'', rfl⟩, rfl, ?_, ?_⟩
      · change χ.vw ℓ'' = t₀
        rw [hχ]; rfl
      · change (fun _ ↦ t₀ : View Loc) ≤ χ.vw
        rw [hχ]; exact le_refl _
  · -- cycles
    rintro χ hχ hcyc
    rcases hχ with hχ | hχ
    · -- an extra message on a cycle would be one of two `κ`-pointed messages
      exfalso
      obtain ⟨b, hrefl, hbmem, -, hbne, hbpt⟩ := Relation.TransGen.tail'_iff.mp hcyc
      have hedge : Gph (S ∪ initialMem v₀ t₀) b χ := ⟨hbmem, Or.inl hχ, hbne, hbpt⟩
      have hbcyc : Relation.TransGen (Gph (S ∪ initialMem v₀ t₀)) b b :=
        Relation.TransGen.head' hedge hrefl
      have hbS : b ∈ S := by
        rcases hbmem with hb | hb
        · exact hb
        · rw [mem_initialMem_iff] at hb
          rw [PointsTo, hb] at hbpt
          exact absurd hbpt.symm (ne_of_gt (hlt χ hχ))
      obtain ⟨c, -, hcmem, -, hcne, hcpt⟩ := Relation.TransGen.tail'_iff.mp hbcyc
      exact hbne (hone b hbS χ hχ (hin b hbS c hcmem hcne hcpt)
        (hin χ hχ b hbmem hbne hbpt))
    · rw [mem_initialMem_iff] at hχ
      refine ⟨Or.inr (by rw [hχ]; exact ⟨χ.lc, rfl⟩), ?_⟩
      rintro χ' (hχ' | hχ') hlceq
      · have h1 : χ.t = t₀ := by rw [hχ]; rfl
        rw [h1]
        exact le_of_lt (hlt χ' hχ')
      · rw [mem_initialMem_iff] at hχ'
        have h1 : χ.t = t₀ := by rw [hχ]; rfl
        have h2 : χ'.t = t₀ := by rw [hχ']; rfl
        rw [h1, h2]

theorem absorbMem_wellFormed (v₀ w v : Val) (t₀ : ℚ) (ℓ : Loc) :
    WellFormed (insert (storedMsg (Loc := Loc) t₀ ℓ w)
      (insert (absMsg t₀ ℓ v) (initialMem v₀ t₀))) := by
  have hset : insert (storedMsg (Loc := Loc) t₀ ℓ w)
      (insert (absMsg t₀ ℓ v) (initialMem v₀ t₀))
      = {storedMsg t₀ ℓ w, absMsg t₀ ℓ v} ∪ initialMem v₀ t₀ := by
    rw [Set.insert_union, Set.singleton_union]
  rw [hset]
  refine union_initialMem_wellFormed v₀ t₀ (fun _ ↦ t₀) _
    ((Set.finite_singleton _).insert _) ?_ ?_ ?_
    (fun ℓ'' ↦ ⟨initialMsg v₀ t₀ ℓ'', Or.inr ⟨ℓ'', rfl⟩, rfl, rfl, le_refl _⟩) ?_ ?_
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl) χ' (rfl | rfl) - ⟨x, hx1, hx2⟩ <;> try rfl
    · simp only [Msg.seg, storedMsg_i, storedMsg_t, absMsg_i, absMsg_t,
        Set.mem_Ioc] at hx1 hx2
      linarith [hx1.2, hx2.1]
    · simp only [Msg.seg, storedMsg_i, storedMsg_t, absMsg_i, absMsg_t,
        Set.mem_Ioc] at hx1 hx2
      linarith [hx1.1, hx2.2]
  · rintro χ (rfl | rfl) χ' (rfl | rfl) h1 h2 <;> first
      | rfl
      | (exfalso; simp only [storedMsg_t, absMsg_t] at h1 h2;
         linarith)

theorem absorbedMem_wellFormed (v₀ v : Val) (t₀ : ℚ) (ℓ : Loc) :
    WellFormed (insert (writeMsg ℓ v t₀ (t₀ + 2) (fun _ ↦ t₀) (by linarith))
      (initialMem (Loc := Loc) v₀ t₀)) := by
  have hset : insert (writeMsg ℓ v t₀ (t₀ + 2) (fun _ ↦ t₀) (by linarith))
      (initialMem (Loc := Loc) v₀ t₀)
      = {writeMsg ℓ v t₀ (t₀ + 2) (fun _ ↦ t₀) (by linarith)} ∪ initialMem v₀ t₀ := by
    rw [Set.singleton_union]
  rw [hset]
  refine union_initialMem_wellFormed v₀ t₀ (fun _ ↦ t₀) _ (Set.finite_singleton _) ?_ ?_ ?_
    (fun ℓ'' ↦ ⟨initialMsg v₀ t₀ ℓ'', Or.inr ⟨ℓ'', rfl⟩, rfl, rfl, le_refl _⟩) ?_ ?_
  · rintro χ rfl; simp
  · rintro χ rfl; simp
  · rintro χ rfl; simp
  · rintro χ rfl χ' rfl - -; rfl
  · rintro χ rfl χ' rfl h1 -
    exfalso
    simp only [writeMsg_t] at h1
    linarith

/-- **`Absorb` merges two dovetailing local writes into one.**  This is the
step the paper's `ℓ ≔ w ; ℓ ≔ v ↠ ℓ ≔ v` example calls for (journal p.37): the
source transition adds `ℓ:w@(t₀,t₀+1]` and `ℓ:v@(t₀+1,t₀+2]` to the initial
memory, the target adds `ℓ:v@(t₀,t₀+2]` alone.  **Original work**: the paper
constructs no trace. -/
theorem absorb_two_writes (v₀ w v : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    TStep gcaRules
      (⟨fun _ ↦ t₀, Chro.single ⟨initialMem v₀ t₀,
          insert (storedMsg t₀ ℓ w) (insert (absMsg t₀ ℓ v) (initialMem v₀ t₀))⟩,
        setView (fun _ ↦ t₀) ℓ (t₀ + 2), r⟩ : PreTrace Loc Val A)
      ⟨fun _ ↦ t₀, Chro.single ⟨initialMem v₀ t₀,
          insert (writeMsg ℓ v t₀ (t₀ + 2) (fun _ ↦ t₀) (by linarith)) (initialMem v₀ t₀)⟩,
        setView (fun _ ↦ t₀) ℓ (t₀ + 2), r⟩ := by
  have hdt := absMsg_dovetail (Val := Val) t₀ ℓ w v
  have hων : (storedMsg (Loc := Loc) t₀ ℓ w).vw ≤ setView (fun _ ↦ t₀) ℓ (t₀ + 2) := hdt.2.2
  have hle : (fun _ ↦ t₀ : View Loc) ≤ setView (fun _ ↦ t₀) ℓ (t₀ + 2) :=
    le_setView (by linarith)
  have hclose : ∀ (S : Memory Loc Val) (χ : Msg Loc Val), χ ∈ S → χ.lc = ℓ →
      χ.t = t₀ + 2 → χ.vw = setView (fun _ ↦ t₀) ℓ (t₀ + 2) →
      initialMem (Loc := Loc) v₀ t₀ ⊆ S →
      PointsDownInto (setView (fun _ ↦ t₀) ℓ (t₀ + 2)) S := by
    intro S χ hχ hlc ht hvw hsub ℓ'
    by_cases hl : ℓ' = ℓ
    · subst hl
      exact ⟨χ, hχ, hlc, by rw [PointsTo, hlc, setView_self, ht], by rw [hvw]⟩
    · exact ⟨initialMsg v₀ t₀ ℓ', hsub ⟨ℓ', rfl⟩, rfl,
        by rw [PointsTo, initialMsg_lc, initialMsg_t, setView_of_ne _ hl], hle⟩
  refine ⟨Step.chro (by simp) (ChroStep.absorb _ _ [] [] (initialMem v₀ t₀)
    (initialMem v₀ t₀) (storedMsg t₀ ℓ w) (absMsg t₀ ℓ v) hdt
    (storedMsg_not_mem_initialMem v₀ t₀ ℓ w) (storedMsg_not_mem_initialMem v₀ t₀ ℓ w)
    ?_ ?_ ?_ ?_ (by simp [listFree]) (by simp [listFree]) (by simp [listFree]) rfl ?_),
    ?_⟩
  · exact writeMsg_not_mem_initialMem v₀ v t₀ (t₀ + 1) (t₀ + 2) ℓ (fun _ ↦ t₀)
      (by linarith) (by linarith)
  · exact writeMsg_not_mem_initialMem v₀ v t₀ (t₀ + 1) (t₀ + 2) ℓ (fun _ ↦ t₀)
      (by linarith) (by linarith)
  · rw [absMsg_setI]
    exact writeMsg_not_mem_initialMem v₀ v t₀ t₀ (t₀ + 2) ℓ (fun _ ↦ t₀)
      (by linarith) (by linarith)
  · rw [absMsg_setI]
    exact writeMsg_not_mem_initialMem v₀ v t₀ t₀ (t₀ + 2) ℓ (fun _ ↦ t₀)
      (by linarith) (by linarith)
  · simp only [Chro.single_toList, List.nil_append, List.map_nil, List.cons.injEq,
      and_true, Transition.mk.injEq, true_and]
    rw [absMsg_setI]
  · refine ⟨?_, pointsDownInto_initialMem v₀ t₀, hle, ?_, ?_⟩
    · intro T hT
      simp only [Chro.single_toList, List.mem_singleton] at hT
      subst hT
      exact ⟨initialMem_wellFormed v₀ t₀, absorbedMem_wellFormed v₀ v t₀ ℓ,
        Set.subset_insert _ _⟩
    · exact hclose _ (writeMsg ℓ v t₀ (t₀ + 2) (fun _ ↦ t₀) (by linarith))
        (Set.mem_insert _ _) rfl (by simp) rfl (Set.subset_insert _ _)
    · intro χ hχ
      simp only [Chro.single_own, Transition.own, Set.mem_diff, Set.mem_insert_iff] at hχ
      obtain ⟨hχ1 | hχ1, hχ2⟩ := hχ
      · subst hχ1
        exact ⟨initialView_le_writeMsg_vw t₀ t₀ (t₀ + 2) ℓ v (by linarith) (by linarith),
          le_refl _, by simp⟩
      · exact absurd hχ1 hχ2

/-- The source of `absorb_two_writes` is a trace. -/
theorem absorb_two_writes_src (v₀ w v : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    IsTrace (⟨fun _ ↦ t₀, Chro.single ⟨initialMem v₀ t₀,
        insert (storedMsg t₀ ℓ w) (insert (absMsg t₀ ℓ v) (initialMem v₀ t₀))⟩,
      setView (fun _ ↦ t₀) ℓ (t₀ + 2), r⟩ : PreTrace Loc Val A) := by
  have hdt := absMsg_dovetail (Val := Val) t₀ ℓ w v
  have hle : (fun _ ↦ t₀ : View Loc) ≤ setView (fun _ ↦ t₀) ℓ (t₀ + 2) :=
    le_setView (by linarith)
  refine ⟨?_, pointsDownInto_initialMem v₀ t₀, hle, ?_, ?_⟩
  · intro T hT
    simp only [Chro.single_toList, List.mem_singleton] at hT
    subst hT
    exact ⟨initialMem_wellFormed v₀ t₀, absorbMem_wellFormed v₀ w v t₀ ℓ,
      (Set.subset_insert _ _).trans (Set.subset_insert _ _)⟩
  · intro ℓ'
    by_cases hl : ℓ' = ℓ
    · subst hl
      exact ⟨absMsg t₀ ℓ' v, Set.mem_insert_of_mem _ (Set.mem_insert _ _), rfl,
        by simp [PointsTo], le_refl _⟩
    · exact ⟨initialMsg v₀ t₀ ℓ',
        Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ ⟨ℓ', rfl⟩), rfl,
        by simp [PointsTo, setView_of_ne _ hl], hle⟩
  · intro χ hχ
    simp only [Chro.single_own, Transition.own, Set.mem_diff, Set.mem_insert_iff] at hχ
    obtain ⟨hχ1 | hχ1 | hχ1, hχ2⟩ := hχ
    · subst hχ1
      exact ⟨initialView_le_storedMsg_vw t₀ ℓ w, hdt.2.2, by simp⟩
    · subst hχ1
      exact ⟨initialView_le_writeMsg_vw t₀ (t₀ + 1) (t₀ + 2) ℓ v (by linarith) (by linarith),
        le_refl _, by simp⟩
    · exact absurd hχ1 hχ2

/-- The `Absorb` step of `absorb_two_writes` is not a `𝔠`-rewriting: it changes
the local messages, which `St`, `Mu`, `Fw`, `Rw` all preserve exactly
(`Refines.own_eq`). -/
theorem not_refines_cRules_absorb (v₀ w v : Val) (t₀ : ℚ) (ℓ : Loc) (r : A) :
    ¬ Refines cRules
      (⟨fun _ ↦ t₀, Chro.single ⟨initialMem v₀ t₀,
          insert (storedMsg t₀ ℓ w) (insert (absMsg t₀ ℓ v) (initialMem v₀ t₀))⟩,
        setView (fun _ ↦ t₀) ℓ (t₀ + 2), r⟩ : PreTrace Loc Val A)
      ⟨fun _ ↦ t₀, Chro.single ⟨initialMem v₀ t₀,
          insert (writeMsg ℓ v t₀ (t₀ + 2) (fun _ ↦ t₀) (by linarith)) (initialMem v₀ t₀)⟩,
        setView (fun _ ↦ t₀) ℓ (t₀ + 2), r⟩ := by
  intro h
  have hown := h.own_eq (subset_refl _) (absorb_two_writes_src v₀ w v t₀ ℓ r)
  simp only [Chro.single_own, Transition.own] at hown
  have hmem : storedMsg (Loc := Loc) t₀ ℓ w ∈
      insert (storedMsg t₀ ℓ w) (insert (absMsg t₀ ℓ v) (initialMem v₀ t₀)) \
        initialMem v₀ t₀ :=
    ⟨Set.mem_insert _ _, storedMsg_not_mem_initialMem v₀ t₀ ℓ w⟩
  rw [hown] at hmem
  simp only [Set.mem_diff, Set.mem_insert_iff] at hmem
  obtain ⟨h1 | h1, -⟩ := hmem
  · have := congrArg Msg.t h1
    simp only [storedMsg_t, writeMsg_t] at this
    linarith
  · exact absurd h1 (storedMsg_not_mem_initialMem v₀ t₀ ℓ w)

end Absorb

/-! ## `Tighten` applied to a local write

The paper's use of `Ti` (journal §E.5, p.59) is to *advance* the view carried by
a local message so that it points at a later message at another location:
*"All that remains is to tighten (Ti) `ℓ:v@(q,t]⟪α[ℓ↦t]⟫` to
`ℓ:v@(q,t]⟪κ[ℓ↦t]⟫`."*  Two locations are essential — at the message's own
location `≤vw` pins the view down, since it fixes the segment — so the memory
below has a second write at `ℓ'` for the tightened view to point at.

**Original work**: the paper constructs no trace.
-/

section Tighten

variable [DecidableEq Loc]

/-- The view that `Tighten` installs: the initial view advanced at `ℓ'` (to
point at the write there) and at `ℓ` (to point at the message carrying it). -/
def tiView (t₀ : ℚ) (ℓ ℓ' : Loc) : View Loc :=
  setView (setView (fun _ ↦ t₀) ℓ' (t₀ + 1)) ℓ (t₀ + 1)

/-- The tightened message: `ℓ:w@(t₀,t₀+1]` carrying `tiView`, which points at
the write at `ℓ'` rather than at the initial message there. -/
def tiMsg (t₀ : ℚ) (ℓ ℓ' : Loc) (w : Val) : Msg Loc Val :=
  writeMsg ℓ w t₀ (t₀ + 1) (setView (fun _ ↦ t₀) ℓ' (t₀ + 1)) (by linarith)

@[simp] theorem tiMsg_lc (t₀ : ℚ) (ℓ ℓ' : Loc) (w : Val) :
    (tiMsg (Val := Val) t₀ ℓ ℓ' w).lc = ℓ := rfl

@[simp] theorem tiMsg_vl (t₀ : ℚ) (ℓ ℓ' : Loc) (w : Val) :
    (tiMsg (Loc := Loc) t₀ ℓ ℓ' w).vl = w := rfl

@[simp] theorem tiMsg_i (t₀ : ℚ) (ℓ ℓ' : Loc) (w : Val) :
    (tiMsg (Loc := Loc) t₀ ℓ ℓ' w).i = t₀ := rfl

@[simp] theorem tiMsg_vw (t₀ : ℚ) (ℓ ℓ' : Loc) (w : Val) :
    (tiMsg (Loc := Loc) t₀ ℓ ℓ' w).vw = tiView t₀ ℓ ℓ' := rfl

@[simp] theorem tiMsg_t (t₀ : ℚ) (ℓ ℓ' : Loc) (w : Val) :
    (tiMsg (Loc := Loc) t₀ ℓ ℓ' w).t = t₀ + 1 := by simp [tiMsg]

theorem setView_mono {κ κ' : View Loc} (h : κ ≤ κ') (ℓ : Loc) (t : ℚ) :
    setView κ ℓ t ≤ setView κ' ℓ t := by
  intro ℓ''
  by_cases hl : ℓ'' = ℓ
  · subst hl; simp
  · rw [setView_of_ne _ hl, setView_of_ne _ hl]; exact h ℓ''

theorem setView_eq_self {κ : View Loc} {ℓ : Loc} {t : ℚ} (h : κ ℓ = t) :
    setView κ ℓ t = κ := by rw [← h]; exact Function.update_eq_self ℓ κ

theorem le_tiView (t₀ : ℚ) (ℓ ℓ' : Loc) : (fun _ ↦ t₀ : View Loc) ≤ tiView t₀ ℓ ℓ' := by
  refine le_trans (le_setView (by simp)) (le_setView ?_)
  by_cases h : ℓ = ℓ'
  · subst h; simp
  · rw [setView_of_ne _ h]; linarith

/-- `Ti`'s premise: the two messages differ only in the view they carry. -/
theorem storedMsg_leVw_tiMsg (t₀ : ℚ) (ℓ ℓ' : Loc) (w : Val) :
    Msg.LeVw (storedMsg (Loc := Loc) t₀ ℓ w) (tiMsg t₀ ℓ ℓ' w) := by
  refine ⟨rfl, rfl, Msg.seg_eq_iff.mpr ⟨rfl, by simp⟩, ?_⟩
  rw [storedMsg_vw, tiMsg_vw, tiView]
  exact setView_mono (le_setView (by simp)) ℓ (t₀ + 1)

@[simp] theorem tiView_self (t₀ : ℚ) (ℓ ℓ' : Loc) : tiView t₀ ℓ ℓ' ℓ = t₀ + 1 :=
  setView_self ..

theorem tiView_other (t₀ : ℚ) {ℓ ℓ' : Loc} (h : ℓ' ≠ ℓ) : tiView t₀ ℓ ℓ' ℓ' = t₀ + 1 := by
  rw [tiView, setView_of_ne _ h, setView_self]

theorem tiView_of_ne {t₀ : ℚ} {ℓ ℓ' ℓ'' : Loc} (h : ℓ'' ≠ ℓ) (h' : ℓ'' ≠ ℓ') :
    tiView t₀ ℓ ℓ' ℓ'' = t₀ := by
  rw [tiView, setView_of_ne _ h, setView_of_ne _ h']

variable [Finite Loc] [Nonempty Loc]

/-- The memory before tightening: the initial memory with a write at `ℓ'` and a
write at `ℓ` whose view points at the *initial* message at `ℓ'`. -/
theorem tightenSrcMem_wellFormed (v₀ u w : Val) (t₀ : ℚ) (ℓ ℓ' : Loc) (hne : ℓ ≠ ℓ') :
    WellFormed (insert (storedMsg (Loc := Loc) t₀ ℓ w) (storedMem v₀ t₀ ℓ' u)) := by
  have hset : insert (storedMsg (Loc := Loc) t₀ ℓ w) (storedMem v₀ t₀ ℓ' u)
      = {storedMsg t₀ ℓ w, storedMsg t₀ ℓ' u} ∪ initialMem v₀ t₀ := by
    rw [Set.insert_union, Set.singleton_union]; rfl
  rw [hset]
  refine union_initialMem_wellFormed v₀ t₀ (fun _ ↦ t₀) _
    ((Set.finite_singleton _).insert _) ?_ ?_ ?_
    (fun ℓ'' ↦ ⟨initialMsg v₀ t₀ ℓ'', Or.inr ⟨ℓ'', rfl⟩, rfl, rfl, le_refl _⟩) ?_ ?_
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl) χ' (rfl | rfl) h - <;> first
      | rfl
      | (exfalso; simp only [storedMsg_lc] at h; exact hne h)
      | (exfalso; simp only [storedMsg_lc] at h; exact hne h.symm)
  · rintro χ (rfl | rfl) χ' (rfl | rfl) h1 h2 <;> first
      | rfl
      | (exfalso; simp only [storedMsg_t] at h1 h2; linarith)

/-- The memory after tightening: the write at `ℓ` now points at the write at
`ℓ'`.  This is where the paper's cycle condition earns its keep — the pointed-at
write is not minimal at its location, so it must not lie on a cycle. -/
theorem tightenTgtMem_wellFormed (v₀ u w : Val) (t₀ : ℚ) (ℓ ℓ' : Loc) (hne : ℓ ≠ ℓ') :
    WellFormed (insert (tiMsg (Loc := Loc) t₀ ℓ ℓ' w) (storedMem v₀ t₀ ℓ' u)) := by
  have hκ : setView (fun _ ↦ t₀) ℓ' (t₀ + 1) ℓ' = t₀ + 1 := setView_self ..
  have hβ : (storedMsg (Loc := Loc) t₀ ℓ' u).vw = setView (fun _ ↦ t₀) ℓ' (t₀ + 1) := rfl
  have hset : insert (tiMsg (Loc := Loc) t₀ ℓ ℓ' w) (storedMem v₀ t₀ ℓ' u)
      = {tiMsg t₀ ℓ ℓ' w, storedMsg t₀ ℓ' u} ∪ initialMem v₀ t₀ := by
    rw [Set.insert_union, Set.singleton_union]; rfl
  rw [hset]
  refine union_initialMem_wellFormed v₀ t₀ (setView (fun _ ↦ t₀) ℓ' (t₀ + 1)) _
    ((Set.finite_singleton _).insert _) ?_ ?_ ?_ ?_ ?_ ?_
  · rintro χ (rfl | rfl) <;> simp
  · rintro χ (rfl | rfl)
    · rw [tiMsg_lc, tiMsg_t, tiMsg_vw, tiView]
    · rw [storedMsg_lc, storedMsg_t, hβ]
      exact (setView_eq_self hκ).symm
  · rintro χ (rfl | rfl)
    · rw [tiMsg_lc, tiMsg_t, setView_of_ne _ hne]; linarith
    · rw [storedMsg_lc, storedMsg_t, hκ]
  · intro ℓ''
    by_cases h : ℓ'' = ℓ'
    · subst h
      refine ⟨storedMsg t₀ ℓ'' u, Or.inl (Set.mem_insert_of_mem _ rfl), rfl, ?_, ?_⟩
      · rw [PointsTo, storedMsg_lc, storedMsg_t]; exact hκ
      · rw [hβ]
    · refine ⟨initialMsg v₀ t₀ ℓ'', Or.inr ⟨ℓ'', rfl⟩, rfl, ?_, ?_⟩
      · rw [PointsTo, initialMsg_lc, initialMsg_t, setView_of_ne _ h]
      · rw [initialMsg_vw]
        exact le_setView (by simp)
  · rintro χ (rfl | rfl) χ' (rfl | rfl) h - <;> first
      | rfl
      | (exfalso; simp only [tiMsg_lc, storedMsg_lc] at h; exact hne h)
      | (exfalso; simp only [tiMsg_lc, storedMsg_lc] at h; exact hne h.symm)
  · rintro χ (rfl | rfl) χ' (rfl | rfl) h1 h2 <;> first
      | rfl
      | (exfalso; simp only [tiMsg_lc, tiMsg_t, storedMsg_lc, storedMsg_t,
           setView_of_ne _ hne] at h1 h2; linarith)

omit [Finite Loc] [Nonempty Loc] in
/-- Both memories of the tighten step close under `tiView`. -/
theorem pointsDownInto_tiView (v₀ u : Val) (t₀ : ℚ) (ℓ ℓ' : Loc) (hne : ℓ ≠ ℓ')
    (S : Memory Loc Val) (χ : Msg Loc Val) (hχ : χ ∈ S) (hlc : χ.lc = ℓ)
    (ht : χ.t = t₀ + 1) (hvw : χ.vw ≤ tiView t₀ ℓ ℓ')
    (hsub : storedMem v₀ t₀ ℓ' u ⊆ S) : PointsDownInto (tiView t₀ ℓ ℓ') S := by
  intro ℓ''
  by_cases h : ℓ'' = ℓ
  · subst h
    exact ⟨χ, hχ, hlc, by rw [PointsTo, hlc, tiView_self, ht], hvw⟩
  · by_cases h' : ℓ'' = ℓ'
    · subst h'
      refine ⟨storedMsg t₀ ℓ'' u, hsub (storedMsg_mem v₀ t₀ ℓ'' u), rfl, ?_, ?_⟩
      · rw [PointsTo, storedMsg_lc, storedMsg_t, tiView_other t₀ h]
      · rw [storedMsg_vw]
        refine le_setView ?_
        rw [setView_of_ne _ (Ne.symm h)]
        linarith
    · refine ⟨initialMsg v₀ t₀ ℓ'', hsub (Set.mem_insert_of_mem _ ⟨ℓ'', rfl⟩), rfl, ?_, ?_⟩
      · rw [PointsTo, initialMsg_lc, initialMsg_t, tiView_of_ne h h']
      · rw [initialMsg_vw]; exact le_tiView t₀ ℓ ℓ'

/-- **`Tighten` advances the view carried by a local write.**  The source memory
has the local write `ℓ:w@(t₀,t₀+1]` whose view points at the *initial* message
at `ℓ'`; the target has the same message carrying `tiView`, which points at the
write `ℓ':u@(t₀,t₀+1]` instead.  This is the shape of the paper's `Ti` step for
write–read reordering (journal §E.5, p.59).  **Original work.** -/
theorem tighten_write (v₀ u w : Val) (t₀ : ℚ) (ℓ ℓ' : Loc) (hne : ℓ ≠ ℓ') (r : A) :
    TStep gcaRules
      (⟨fun _ ↦ t₀, Chro.single ⟨storedMem v₀ t₀ ℓ' u,
          insert (storedMsg t₀ ℓ w) (storedMem v₀ t₀ ℓ' u)⟩,
        tiView t₀ ℓ ℓ', r⟩ : PreTrace Loc Val A)
      ⟨fun _ ↦ t₀, Chro.single ⟨storedMem v₀ t₀ ℓ' u,
          insert (tiMsg t₀ ℓ ℓ' w) (storedMem v₀ t₀ ℓ' u)⟩,
        tiView t₀ ℓ ℓ', r⟩ := by
  have hlvw := storedMsg_leVw_tiMsg (Val := Val) t₀ ℓ ℓ' w
  have hνμ : storedMsg (Loc := Loc) t₀ ℓ w ∉ storedMem v₀ t₀ ℓ' u := by
    rintro (h | h)
    · exact hne (congrArg Msg.lc h)
    · exact storedMsg_not_mem_initialMem v₀ t₀ ℓ w h
  have hεμ : tiMsg (Loc := Loc) t₀ ℓ ℓ' w ∉ storedMem v₀ t₀ ℓ' u := by
    rintro (h | h)
    · exact hne (congrArg Msg.lc h)
    · exact writeMsg_not_mem_initialMem v₀ w t₀ t₀ (t₀ + 1) ℓ
        (setView (fun _ ↦ t₀) ℓ' (t₀ + 1)) (by linarith) (by linarith) h
  refine ⟨Step.chro (by simp) (ChroStep.tighten _ _ [] [] (storedMem v₀ t₀ ℓ' u)
    (storedMem v₀ t₀ ℓ' u) (storedMsg t₀ ℓ w) (tiMsg t₀ ℓ ℓ' w) hlvw hνμ hνμ hεμ hεμ
    (by simp [listFree]) (by simp [listFree]) rfl rfl), ?_⟩
  refine ⟨?_, (pointsDownInto_initialMem v₀ t₀).mono (initialMem_subset_storedMem v₀ t₀ ℓ' u),
    le_tiView t₀ ℓ ℓ', ?_, ?_⟩
  · intro T hT
    simp only [Chro.single_toList, List.mem_singleton] at hT
    subst hT
    exact ⟨storedMem_wellFormed v₀ t₀ ℓ' u, tightenTgtMem_wellFormed v₀ u w t₀ ℓ ℓ' hne,
      Set.subset_insert _ _⟩
  · exact pointsDownInto_tiView v₀ u t₀ ℓ ℓ' hne _ (tiMsg t₀ ℓ ℓ' w)
      (Set.mem_insert _ _) rfl (by simp) (le_refl _) (Set.subset_insert _ _)
  · intro χ hχ
    simp only [Chro.single_own, Transition.own, Set.mem_diff, Set.mem_insert_iff] at hχ
    obtain ⟨hχ1 | hχ1, hχ2⟩ := hχ
    · subst hχ1
      exact ⟨le_tiView t₀ ℓ ℓ', le_refl _, by simp⟩
    · exact absurd hχ1 hχ2

/-- The source of `tighten_write` is a trace. -/
theorem tighten_write_src (v₀ u w : Val) (t₀ : ℚ) (ℓ ℓ' : Loc) (hne : ℓ ≠ ℓ') (r : A) :
    IsTrace (⟨fun _ ↦ t₀, Chro.single ⟨storedMem v₀ t₀ ℓ' u,
        insert (storedMsg t₀ ℓ w) (storedMem v₀ t₀ ℓ' u)⟩,
      tiView t₀ ℓ ℓ', r⟩ : PreTrace Loc Val A) := by
  have hlvw := storedMsg_leVw_tiMsg (Val := Val) t₀ ℓ ℓ' w
  refine ⟨?_, (pointsDownInto_initialMem v₀ t₀).mono (initialMem_subset_storedMem v₀ t₀ ℓ' u),
    le_tiView t₀ ℓ ℓ', ?_, ?_⟩
  · intro T hT
    simp only [Chro.single_toList, List.mem_singleton] at hT
    subst hT
    exact ⟨storedMem_wellFormed v₀ t₀ ℓ' u, tightenSrcMem_wellFormed v₀ u w t₀ ℓ ℓ' hne,
      Set.subset_insert _ _⟩
  · exact pointsDownInto_tiView v₀ u t₀ ℓ ℓ' hne _ (storedMsg t₀ ℓ w)
      (Set.mem_insert _ _) rfl (by simp) hlvw.2.2.2 (Set.subset_insert _ _)
  · intro χ hχ
    simp only [Chro.single_own, Transition.own, Set.mem_diff, Set.mem_insert_iff] at hχ
    obtain ⟨hχ1 | hχ1, hχ2⟩ := hχ
    · subst hχ1
      exact ⟨initialView_le_storedMsg_vw t₀ ℓ w, hlvw.2.2.2, by simp⟩
    · exact absurd hχ1 hχ2

/-- The `Tighten` step of `tighten_write` is not a `𝔠`-rewriting: it changes the
local messages, which the `𝔠` rules preserve exactly. -/
theorem not_refines_cRules_tighten (v₀ u w : Val) (t₀ : ℚ) (ℓ ℓ' : Loc) (hne : ℓ ≠ ℓ')
    (r : A) :
    ¬ Refines cRules
      (⟨fun _ ↦ t₀, Chro.single ⟨storedMem v₀ t₀ ℓ' u,
          insert (storedMsg t₀ ℓ w) (storedMem v₀ t₀ ℓ' u)⟩,
        tiView t₀ ℓ ℓ', r⟩ : PreTrace Loc Val A)
      ⟨fun _ ↦ t₀, Chro.single ⟨storedMem v₀ t₀ ℓ' u,
          insert (tiMsg t₀ ℓ ℓ' w) (storedMem v₀ t₀ ℓ' u)⟩,
        tiView t₀ ℓ ℓ', r⟩ := by
  intro h
  have hνμ : storedMsg (Loc := Loc) t₀ ℓ w ∉ storedMem v₀ t₀ ℓ' u := by
    rintro (h' | h')
    · exact hne (congrArg Msg.lc h')
    · exact storedMsg_not_mem_initialMem v₀ t₀ ℓ w h'
  have hown := h.own_eq (subset_refl _) (tighten_write_src v₀ u w t₀ ℓ ℓ' hne r)
  simp only [Chro.single_own, Transition.own] at hown
  have hmem : storedMsg (Loc := Loc) t₀ ℓ w ∈
      insert (storedMsg t₀ ℓ w) (storedMem v₀ t₀ ℓ' u) \ storedMem v₀ t₀ ℓ' u :=
    ⟨Set.mem_insert _ _, hνμ⟩
  rw [hown] at hmem
  simp only [Set.mem_diff, Set.mem_insert_iff] at hmem
  obtain ⟨h1 | h1, -⟩ := hmem
  · have := congrArg Msg.vw h1
    simp only [storedMsg_vw, tiMsg_vw] at this
    have h2 := congrFun this ℓ'
    rw [setView_of_ne _ (Ne.symm hne), tiView_other t₀ (Ne.symm hne)] at h2
    linarith
  · exact hνμ h1

end Tighten

end Isotope.Elgot.RA
