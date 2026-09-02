import Isotope.Elgot.Brookes.TSO.Interleaving

/-!
# Store buffering is impossible under sequential consistency

The write-then-read invariant of `Isotope/Elgot/Brookes/TSO/Invariant.lean` and
the impossibility argument of `Isotope/Elgot/Brookes/TSO/Litmus.lean`, restated
over the **plain** sequentially consistent state `SeqCst.Store Loc Val = Loc → Val`
with `SeqCst.write` and `SeqCst.read`, rather than over the store-plus-buffer
state `TSO.St Tid Loc Val`.

The TSO files prove the same thing at `Tid := PUnit`, but their state carries a
vestigial per-thread write buffer that `writeSC`/`readSC` never touch.  The
separation theorem of `Isotope/Elgot/Opt/StoreBuffering.lean` is a comparison
with the release/acquire model, so it should be stated against the standard
Brookes model of sequential consistency and nothing else; that is what this file
supplies.  The proofs are the TSO ones with `p.2.mem` replaced by `p.2`.

## What "impossible" means here

The statement is about **interference-free** executions: `Seq μ t μ'` says every
gap between successive rely-guarantee pairs of `t` is closed, so `t` is a run of
the *closed* system.  This side condition cannot be dropped.  In the open,
compositional order the sequentially consistent model *does* admit the outcome
`⟨v₀, v₀⟩`, because the environment may restore `x` to `v₀` between the two
threads' steps.  Every litmus test in the memory-model literature lives at this
projection.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {Loc Val : Type u}

/-- A sequentially consistent Brookes trace: a word of rely-guarantee pairs over
the store. -/
abbrev Tr (Loc Val : Type u) : Type u := Trace (Store Loc Val × Store Loc Val)

/-! ## Interference-free executions -/

/-- `Seq μ t μ'`: the trace `t` is a complete execution from `μ` to `μ'` with no
environment interference — every gap between successive rely-guarantee pairs is
closed.  These are the runs of the closed system. -/
inductive Seq : Store Loc Val → Tr Loc Val → Store Loc Val → Prop
  | /-- The empty execution. -/
    nil {μ : Store Loc Val} : Seq μ [] μ
  | /-- One step, taken from the current state. -/
    cons {μ ρ : Store Loc Val} {t : Tr Loc Val} {σ : Store Loc Val} :
      Seq ρ t σ → Seq μ ((μ, ρ) :: t) σ

/-- Stuttering and mumbling *reflect* interference-free executions: if a rewrite
of `t` is interference-free, so was `t`, with the same endpoints.  This is why
the impossibility argument may be run on the closed trace set. -/
theorem Seq.of_step {t t' : Tr Loc Val} (h : Step (Store Loc Val) t t')
    {μ σ : Store Loc Val} (hs : Seq μ t' σ) : Seq μ t σ := by
  induction h generalizing μ with
  | stutter ρ t => cases hs with | cons h => exact h
  | mumble ρ θ ν t => cases hs with | cons h => exact .cons (.cons h)
  | cons p _ ih =>
    obtain ⟨q, q'⟩ := p
    cases hs with | cons h => exact .cons (ih h)

/-- Refinement reflects interference-free executions. -/
theorem Seq.of_refines {t t' : Tr Loc Val}
    (h : (rewriting (Store Loc Val)).Refines t t')
    {μ σ : Store Loc Val} (hs : Seq μ t' σ) : Seq μ t σ := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact ih (Seq.of_step hstep hs)

/-- An empty interference-free execution changes nothing. -/
theorem Seq.nil_eq {μ σ : Store Loc Val} (h : Seq μ ([] : Tr Loc Val) σ) : μ = σ := by
  cases h; rfl

/-! ## The write-then-read invariant -/

variable [DecidableEq Loc]

/-- A step whose only effect on the store is, possibly, to write `v` at `ℓ`. -/
def OkStep (ℓ : Loc) (v : Val) (p : Store Loc Val × Store Loc Val) : Prop :=
  p.2 = p.1 ∨ p.2 = Function.update p.1 ℓ v

/-- A stutter is harmless. -/
theorem okStep_stutter (ℓ : Loc) (v : Val) (μ : Store Loc Val) : OkStep ℓ v (μ, μ) :=
  Or.inl rfl

/-- An `OkStep` leaves every other location alone. -/
theorem OkStep.mem_ne {ℓ k : Loc} {v : Val} {p : Store Loc Val × Store Loc Val}
    (h : OkStep ℓ v p) (hk : k ≠ ℓ) : p.2 k = p.1 k := by
  rcases h with h | h <;> rw [h]
  exact Function.update_of_ne hk _ _

/-- Once the store holds `v` at `ℓ`, an `OkStep` keeps it there. -/
theorem OkStep.keeps {ℓ : Loc} {v : Val} {p : Store Loc Val × Store Loc Val}
    (h : OkStep ℓ v p) (h1 : p.1 ℓ = v) : p.2 ℓ = v := by
  rcases h with h | h <;> rw [h]
  · exact h1
  · exact Function.update_self _ _ _

/-- Two composable `OkStep`s compose: this is what makes the invariant survive
mumbling. -/
theorem OkStep.trans {ℓ : Loc} {v : Val} {μ ρ θ : Store Loc Val}
    (h₁ : OkStep ℓ v (μ, ρ)) (h₂ : OkStep ℓ v (ρ, θ)) : OkStep ℓ v (μ, θ) := by
  rcases h₁ with h₁ | h₁ <;> rcases h₂ with h₂ | h₂ <;> simp only [] at h₁ h₂ ⊢
  · exact Or.inl (h₂.trans h₁)
  · exact Or.inr (by rw [h₂, h₁])
  · exact Or.inr (by rw [h₂, h₁])
  · exact Or.inr (by rw [h₂, h₁, Function.update_idem])

/-- Every step of the trace is an `OkStep`. -/
def OkAll (ℓ : Loc) (v : Val) (t : Tr Loc Val) : Prop := ∀ p ∈ t, OkStep ℓ v p

@[simp] theorem okAll_nil (ℓ : Loc) (v : Val) : OkAll ℓ v ([] : Tr Loc Val) := by
  intro p hp; exact absurd hp List.not_mem_nil

theorem OkAll.head {ℓ : Loc} {v : Val} {p : Store Loc Val × Store Loc Val}
    {t : Tr Loc Val} (h : OkAll ℓ v (p :: t)) : OkStep ℓ v p := h p (by simp)

theorem OkAll.tail {ℓ : Loc} {v : Val} {p : Store Loc Val × Store Loc Val}
    {t : Tr Loc Val} (h : OkAll ℓ v (p :: t)) : OkAll ℓ v t :=
  fun q hq ↦ h q (by simp [hq])

theorem OkAll.cons {ℓ : Loc} {v : Val} {p : Store Loc Val × Store Loc Val}
    {t : Tr Loc Val} (hp : OkStep ℓ v p) (ht : OkAll ℓ v t) : OkAll ℓ v (p :: t) := by
  intro q hq
  rcases List.mem_cons.1 hq with rfl | hq
  · exact hp
  · exact ht q hq

/-- `OkAll` survives one stuttering or mumbling rewrite. -/
theorem okAll_step {ℓ : Loc} {v : Val} {t t' : Tr Loc Val}
    (h : Step (Store Loc Val) t t') : OkAll ℓ v t → OkAll ℓ v t' := by
  induction h with
  | stutter μ t => exact fun ht ↦ OkAll.cons (okStep_stutter ℓ v μ) ht
  | mumble μ ρ θ t =>
    exact fun ht ↦ OkAll.cons (OkStep.trans ht.head ht.tail.head) ht.tail.tail
  | cons q _ ih => exact fun ht ↦ OkAll.cons ht.head (ih ht.tail)

/-- `OkAll` survives refinement. -/
theorem OkAll.refines {ℓ : Loc} {v : Val} {t t' : Tr Loc Val}
    (h : (rewriting (Store Loc Val)).Refines t t') (ht : OkAll ℓ v t) : OkAll ℓ v t' := by
  induction h with
  | refl => exact ht
  | tail _ hstep ih => exact okAll_step hstep ih

/-- `Reads ℓ v k r t`: every step of `t` writes at most `ℓ := v`, and some step
observes the value `r` at `k`. -/
inductive Reads (ℓ : Loc) (v : Val) (k : Loc) (r : Val) : Tr Loc Val → Prop
  | /-- The observation happens now. -/
    here {p : Store Loc Val × Store Loc Val} {t : Tr Loc Val} :
      OkStep ℓ v p → p.2 k = r → OkAll ℓ v t → Reads ℓ v k r (p :: t)
  | /-- The observation happens later. -/
    there {p : Store Loc Val × Store Loc Val} {t : Tr Loc Val} :
      OkStep ℓ v p → Reads ℓ v k r t → Reads ℓ v k r (p :: t)

theorem Reads.okAll {ℓ : Loc} {v : Val} {k : Loc} {r : Val} {t : Tr Loc Val}
    (h : Reads ℓ v k r t) : OkAll ℓ v t := by
  induction h with
  | here hp _ ht => exact OkAll.cons hp ht
  | there hp _ ih => exact OkAll.cons hp ih

/-- `Reads` survives one rewrite, provided the location read is not the location
written. -/
theorem reads_step {ℓ : Loc} {v : Val} {k : Loc} {r : Val} (hk : k ≠ ℓ)
    {t t' : Tr Loc Val} (h : Step (Store Loc Val) t t') :
    Reads ℓ v k r t → Reads ℓ v k r t' := by
  induction h with
  | stutter μ t => exact fun ht ↦ .there (okStep_stutter ℓ v μ) ht
  | mumble μ ρ θ t =>
    intro ht
    cases ht with
    | here hp hr hall =>
      exact .here (hp.trans hall.head) ((hall.head.mem_ne hk).trans hr) hall.tail
    | there hp ht' =>
      cases ht' with
      | here hq hr hall => exact .here (hp.trans hq) hr hall
      | there hq ht'' => exact .there (hp.trans hq) ht''
  | cons q hstep ih =>
    intro ht
    cases ht with
    | here hp hr hall => exact .here hp hr (okAll_step hstep hall)
    | there hp ht' => exact .there hp (ih ht')

/-- `Reads` survives refinement. -/
theorem Reads.refines {ℓ : Loc} {v : Val} {k : Loc} {r : Val} (hk : k ≠ ℓ)
    {t t' : Tr Loc Val} (h : (rewriting (Store Loc Val)).Refines t t')
    (ht : Reads ℓ v k r t) : Reads ℓ v k r t' := by
  induction h with
  | refl => exact ht
  | tail _ hstep ih => exact reads_step hk hstep ih

/-- `Wrote ℓ v k r t`: some step of `t` leaves `v` in the store at `ℓ`, and the
observation of `r` at `k` happens at or after that step. -/
inductive Wrote (ℓ : Loc) (v : Val) (k : Loc) (r : Val) : Tr Loc Val → Prop
  | /-- The write lands now, and the read follows. -/
    write {p : Store Loc Val × Store Loc Val} {t : Tr Loc Val} :
      OkStep ℓ v p → p.2 ℓ = v → Reads ℓ v k r (p :: t) → Wrote ℓ v k r (p :: t)
  | /-- The write has not landed yet. -/
    skip {p : Store Loc Val × Store Loc Val} {t : Tr Loc Val} :
      OkStep ℓ v p → Wrote ℓ v k r t → Wrote ℓ v k r (p :: t)

theorem Wrote.okAll {ℓ : Loc} {v : Val} {k : Loc} {r : Val} {t : Tr Loc Val}
    (h : Wrote ℓ v k r t) : OkAll ℓ v t := by
  induction h with
  | write _ _ hr => exact hr.okAll
  | skip hp _ ih => exact OkAll.cons hp ih

/-- `Wrote` survives one rewrite. -/
theorem wrote_step {ℓ : Loc} {v : Val} {k : Loc} {r : Val} (hk : k ≠ ℓ)
    {t t' : Tr Loc Val} (h : Step (Store Loc Val) t t') :
    Wrote ℓ v k r t → Wrote ℓ v k r t' := by
  induction h with
  | stutter μ t => exact fun ht ↦ .skip (okStep_stutter ℓ v μ) ht
  | mumble μ ρ θ t =>
    intro ht
    cases ht with
    | write hp hset hreads =>
      have hq : OkStep ℓ v ((ρ, θ) : Store Loc Val × Store Loc Val) :=
        hreads.okAll.tail.head
      exact .write (hp.trans hq) (hq.keeps hset)
        (reads_step hk (Step.mumble μ ρ θ t) hreads)
    | skip hp ht' =>
      cases ht' with
      | write hq hset hreads =>
        refine .write (hp.trans hq) hset ?_
        cases hreads with
        | here _ hr hall => exact .here (hp.trans hq) hr hall
        | there _ hrest => exact .there (hp.trans hq) hrest
      | skip hq ht'' => exact .skip (hp.trans hq) ht''
  | cons q hstep ih =>
    intro ht
    cases ht with
    | write hp hset hreads =>
      exact .write hp hset (reads_step hk (Step.cons q hstep) hreads)
    | skip hp ht' => exact .skip hp (ih ht')

/-- **`Wrote` survives refinement**, so it is a property of the *closed* trace
set of a computation and not merely of its generators.  This is what makes the
impossibility argument apply to the Brookes denotation rather than to a choice
of representative traces. -/
theorem Wrote.refines {ℓ : Loc} {v : Val} {k : Loc} {r : Val} (hk : k ≠ ℓ)
    {t t' : Tr Loc Val} (h : (rewriting (Store Loc Val)).Refines t t')
    (ht : Wrote ℓ v k r t) : Wrote ℓ v k r t' := by
  induction h with
  | refl => exact ht
  | tail _ hstep ih => exact wrote_step hk hstep ih

/-! ## The four propagation lemmas -/

variable {x y : Loc} {v0 v1 : Val}

/-- If the location thread 1 is waiting to read already holds `v1`, and thread 2
never writes anything else there, thread 1 cannot read `v0`. -/
theorem reads_absurd (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Loc Val}
    (hi : Interleave t₁ t₂ t) :
    ∀ {μ σ : Store Loc Val}, Seq μ t σ → Reads x v1 y v0 t₁ → OkAll y v1 t₂ →
      μ y = v1 → False := by
  induction hi with
  | nil => intro μ σ _ h₁ _ _; cases h₁
  | @left e t₁' t₂' w _ ih =>
    intro μ σ hs h₁ h₂ hy
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₁ with
      | here hp hr _ => exact hv (hr.symm.trans ((hp.mem_ne (Ne.symm hxy)).trans hy))
      | there hp h₁' => exact ih hs' h₁' h₂ ((hp.mem_ne (Ne.symm hxy)).trans hy)
  | @right e t₁' t₂' w _ ih =>
    intro μ σ hs h₁ h₂ hy
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' => exact ih hs' h₁ h₂.tail (h₂.head.keeps hy)

/-- The mirror image of `reads_absurd`, with the two threads exchanged. -/
theorem reads_absurd' (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Loc Val}
    (hi : Interleave t₁ t₂ t) {μ σ : Store Loc Val} (hs : Seq μ t σ)
    (h₁ : OkAll x v1 t₁) (h₂ : Reads y v1 x v0 t₂) (hx : μ x = v1) : False :=
  reads_absurd (Ne.symm hxy) hv hi.swap hs h₂ h₁ hx

/-- If the location thread 2 will read already holds `v1`, thread 2's pending
`write`-then-`read` cannot complete with the value `v0`. -/
theorem wrote_absurd (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Loc Val}
    (hi : Interleave t₁ t₂ t) :
    ∀ {μ σ : Store Loc Val}, Seq μ t σ → OkAll x v1 t₁ → Wrote y v1 x v0 t₂ →
      μ x = v1 → False := by
  induction hi with
  | nil => intro μ σ _ _ h₂ _; cases h₂
  | @left e t₁' t₂' w _ ih =>
    intro μ σ hs h₁ h₂ hx
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' => exact ih hs' h₁.tail h₂ (h₁.head.keeps hx)
  | @right e t₁' t₂' w hi' ih =>
    intro μ σ hs h₁ h₂ hx
    cases h₂ with
    | write _ _ hreads => exact reads_absurd' hxy hv (Interleave.right hi') hs h₁ hreads hx
    | skip hp h₂' =>
      obtain ⟨q, q'⟩ := e
      cases hs with
      | cons hs' => exact ih hs' h₁ h₂' ((hp.mem_ne hxy).trans hx)

/-- Thread 1 is about to read `v0` from `y`, thread 2 still owes its write to `y`
and its read of `x`, and `x` already holds `v1`: impossible. -/
theorem reads_wrote_absurd (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Loc Val}
    (hi : Interleave t₁ t₂ t) :
    ∀ {μ σ : Store Loc Val}, Seq μ t σ → Reads x v1 y v0 t₁ → Wrote y v1 x v0 t₂ →
      μ y = v0 → μ x = v1 → False := by
  induction hi with
  | nil => intro μ σ _ h₁ _ _ _; cases h₁
  | @left e t₁' t₂' w hi' ih =>
    intro μ σ hs h₁ h₂ hy hx
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₁ with
      | here hp _ hall => exact wrote_absurd hxy hv hi' hs' hall h₂ (hp.keeps hx)
      | there hp h₁' =>
        exact ih hs' h₁' h₂ ((hp.mem_ne (Ne.symm hxy)).trans hy) (hp.keeps hx)
  | @right e t₁' t₂' w hi' ih =>
    intro μ σ hs h₁ h₂ hy hx
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₂ with
      | write _ hset hreads =>
        exact reads_absurd hxy hv hi' hs' h₁ hreads.okAll.tail hset
      | skip hp h₂' =>
        rcases hp with hmem | hmem
        · exact ih hs' h₁ h₂' (by rw [show q' = μ from hmem]; exact hy)
            (by rw [show q' = μ from hmem]; exact hx)
        · refine reads_absurd hxy hv hi' hs' h₁ h₂'.okAll ?_
          rw [show q' = Function.update μ y v1 from hmem]
          exact Function.update_self _ _ _

/-- **Store buffering is impossible for two `Wrote` threads.**  If each thread
puts `v1` into the store at its own location *before* observing the other's, and
both observe `v0`, the two orderings contradict. -/
theorem store_buffering_absurd (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Loc Val}
    (hi : Interleave t₁ t₂ t) :
    ∀ {μ σ : Store Loc Val}, Seq μ t σ → Wrote x v1 y v0 t₁ → Wrote y v1 x v0 t₂ →
      μ x = v0 → μ y = v0 → False := by
  induction hi with
  | nil => intro μ σ _ h₁ _ _ _; cases h₁
  | @left e t₁' t₂' w hi' ih =>
    intro μ σ hs h₁ h₂ hx hy
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₁ with
      | write hp hset hreads =>
        cases hreads with
        | here _ _ hall => exact wrote_absurd hxy hv hi' hs' hall h₂ hset
        | there _ hreads' =>
          exact reads_wrote_absurd hxy hv hi' hs' hreads' h₂
            ((hp.mem_ne (Ne.symm hxy)).trans hy) hset
      | skip hp h₁' =>
        rcases hp with hmem | hmem
        · exact ih hs' h₁' h₂ (by rw [show q' = μ from hmem]; exact hx)
            (by rw [show q' = μ from hmem]; exact hy)
        · refine wrote_absurd hxy hv hi' hs' h₁'.okAll h₂ ?_
          rw [show q' = Function.update μ x v1 from hmem]
          exact Function.update_self _ _ _
  | @right e t₁' t₂' w hi' ih =>
    intro μ σ hs h₁ h₂ hx hy
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₂ with
      | write hp hset hreads =>
        cases hreads with
        | here _ _ hall =>
          exact wrote_absurd (Ne.symm hxy) hv hi'.swap hs' hall h₁ hset
        | there _ hreads' =>
          exact reads_wrote_absurd (Ne.symm hxy) hv hi'.swap hs' hreads' h₁
            ((hp.mem_ne hxy).trans hx) hset
      | skip hp h₂' =>
        rcases hp with hmem | hmem
        · exact ih hs' h₁ h₂' (by rw [show q' = μ from hmem]; exact hx)
            (by rw [show q' = μ from hmem]; exact hy)
        · refine wrote_absurd (Ne.symm hxy) hv hi'.swap hs' h₂'.okAll h₁ ?_
          rw [show q' = Function.update μ y v1 from hmem]
          exact Function.update_self _ _ _

/-! ## The store-buffering program and the impossibility theorem -/

/-- One store-buffering thread: write `v` to `wl`, then read `rl`. -/
def sb (wl rl : Loc) (v : Val) : Comp Loc Val Val :=
  write wl v >>= fun _ ↦ read rl

/-- Every execution of a thread writes to the store before it reads.  This is the
whole content of "sequential consistency" here, and it holds of the *closed*
trace set because `Wrote` survives stuttering and mumbling. -/
theorem sb_wrote {wl rl : Loc} (hk : rl ≠ wl) {t : Tr Loc Val} {r : Val}
    (h : (t, r) ∈ sb wl rl v1) : Wrote wl v1 rl r t := by
  obtain ⟨a, u, v, hu, hv, hr⟩ := (Brookes.mem_bind_iff _ _ _ _).1 h
  obtain ⟨u₀, hu₀, hu'⟩ := hu
  obtain ⟨μ, hμ⟩ := hu₀
  obtain ⟨v₀, hv₀, hv'⟩ := hv
  obtain ⟨ρ, hρ, hrv⟩ := hv₀
  have hraw : Wrote wl v1 rl r ([(μ, Function.update μ wl v1)] ++ [(ρ, ρ)]) :=
    .write (Or.inr rfl) (Function.update_self _ _ _)
      (.there (Or.inr rfl) (.here (okStep_stutter _ _ _) hrv.symm (okAll_nil _ _)))
  refine Wrote.refines hk ((Rewriting.refines_append ?_ ?_).trans hr) hraw
  · exact hμ ▸ hu'
  · exact hρ ▸ hv'

/-- **Sequential consistency forbids store buffering.**  No interference-free
execution of

```
(x := v₁ ; y?)  ∥  (y := v₁ ; x?)
```

started from a store in which both locations hold `v₀`, has both threads read
`v₀`.

Stated over the plain Brookes state `Store Loc Val = Loc → Val`, with the
paper's `write` and the dual `read`, and over `Brookes.par`, which is trace
interleaving followed by the stuttering/mumbling closure.  The interference-free
side condition `Seq μ t σ` is essential: in the open order the environment can
restore `x` to `v₀` and the outcome becomes possible. -/
theorem sc_forbids_store_buffering (hxy : x ≠ y) (hv : v0 ≠ v1)
    {μ σ : Store Loc Val} (hx : μ x = v0) (hy : μ y = v0)
    {t : Tr Loc Val} (hseq : Seq μ t σ) :
    (t, (v0, v0)) ∉ par (sb x y v1) (sb y x v1) := by
  intro hmem
  obtain ⟨w₀, t₁, t₂, h₁, h₂, hi, hr⟩ := mem_par_iff.1 hmem
  exact store_buffering_absurd hxy hv hi (Seq.of_refines hr hseq)
    (sb_wrote (Ne.symm hxy) h₁) (sb_wrote hxy h₂) hx hy

end SeqCst

end Isotope.Elgot.Brookes
