import Isotope.Elgot.Brookes.SeqCst.Parallel

/-!
# Chains, blocks, and a normal form for stutter/mumble refinement

This file supplies the combinatorial content that Brookes's full-abstraction
proof elides.  In the negative half of the definability argument he writes:

> "But it is easy to see that this is possible only if `α` itself is derivable
> from `α'` by stuttering and mumbling."
> — *Full Abstraction for a Shared-Variable Parallel Language*, journal p. 152.

Everything here is **ours**, not the paper's: the paper states no lemma of this
kind.  Two notions do the work.

* `Chain s t s'` — the trace `t` is an *interference-free* execution from `s` to
  `s'`: every guarantee is the next rely.  Brookes calls such traces
  interference-free (journal p. 149).
* `Chunk t t'` — `t` splits into consecutive, possibly empty, blocks, one per
  pair of `t'`, each block a chain between that pair's two states.

`chunk_iff_refines` shows `Chunk` *is* stutter/mumble refinement.  An empty block
is a stutter; a block of length ≥ 2 is iterated mumbling.  Two consequences drive
the rest of the development:

* `chain_iff_refines_single` — refining down to a single pair is exactly being an
  interference-free execution between its two states;
* `chunk_of_interleave_chain` (**Key Lemma**) — if a shuffle of `t` with `u` is
  interference-free from `s` to `s'`, then cutting it at the `u`-pairs exhibits
  `t` as a `Chunk` of `zip s u s'`.  This is the "easy to see" step.

`zip s u s'` reconstructs Brookes's trace `α` from the trace `ᾱ = u` of the
separating context `DO_α` and the two observed endpoints; `merge` is the
alternating shuffle he uses for the positive half.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {S : Type u}

/-! ## Interference-free executions -/

/-- `Chain s t s'`: the trace `t` is a complete, interference-free execution from
`s` to `s'` — every gap between successive rely-guarantee pairs is closed. -/
inductive Chain : S → Trace (S × S) → S → Prop
  | /-- The empty execution changes nothing. -/
    nil (s : S) : Chain s [] s
  | /-- One step, taken from the current state. -/
    cons (s m : S) {t : Trace (S × S)} {s' : S} : Chain m t s' → Chain s ((s, m) :: t) s'

/-- An empty interference-free execution has equal endpoints. -/
theorem Chain.nil_inv {s s' : S} (h : Chain s [] s') : s = s' := by cases h; rfl

/-- Inversion for a nonempty interference-free execution. -/
theorem Chain.cons_inv : ∀ {s : S} {w : Trace (S × S)} {s' : S}, Chain s w s' →
    ∀ {e : S × S} {w₀ : Trace (S × S)}, w = e :: w₀ → e.1 = s ∧ Chain e.2 w₀ s' := by
  intro s w s' h
  cases h with
  | nil s => intro e w₀ hw; exact absurd hw (by simp)
  | cons s m h => intro e w₀ hw; cases hw; exact ⟨rfl, h⟩

/-- Interference-free executions compose. -/
theorem Chain.append {s m s' : S} {t u : Trace (S × S)} (h : Chain s t m) (h' : Chain m u s') :
    Chain s (t ++ u) s' := by
  induction h with
  | nil s => exact h'
  | cons s m' _ ih => exact .cons s m' (ih h')

/-- An interference-free execution splits wherever its trace splits. -/
theorem Chain.split : ∀ {t : Trace (S × S)} {s : S} {u : Trace (S × S)} {s' : S},
    Chain s (t ++ u) s' → ∃ m, Chain s t m ∧ Chain m u s' := by
  intro t
  induction t with
  | nil => intro s u s' h; exact ⟨s, .nil s, h⟩
  | cons e t ih =>
      intro s u s' h
      obtain ⟨e₁, e₂⟩ := e
      obtain ⟨rfl, h'⟩ := h.cons_inv rfl
      obtain ⟨m, h₁, h₂⟩ := ih h'
      exact ⟨m, .cons _ _ h₁, h₂⟩

/-! ## Blocks -/

/-- `Chunk t t'`: the trace `t` splits into consecutive, possibly empty, blocks,
one for each pair of `t'`, each block an interference-free execution between the
rely and the guarantee of its pair. -/
inductive Chunk : Trace (S × S) → Trace (S × S) → Prop
  | /-- No blocks. -/
    nil : Chunk [] []
  | /-- One more block, accounting for one more pair. -/
    cons {b t : Trace (S × S)} {x y : S} {t' : Trace (S × S)} :
      Chain x b y → Chunk t t' → Chunk (b ++ t) ((x, y) :: t')

/-- Only the empty trace is chunked by the empty trace. -/
theorem Chunk.nil_inv : ∀ {t r : Trace (S × S)}, Chunk t r → r = [] → t = [] := by
  intro t r h
  cases h with
  | nil => intro _; rfl
  | cons _ _ => intro hr; exact absurd hr (by simp)

/-- Inversion: the first pair of the right-hand trace accounts for a prefix
block of the left-hand one. -/
theorem Chunk.cons_inv : ∀ {t r : Trace (S × S)}, Chunk t r →
    ∀ {x y : S} {t' : Trace (S × S)}, r = (x, y) :: t' →
      ∃ b t₂, t = b ++ t₂ ∧ Chain x b y ∧ Chunk t₂ t' := by
  intro t r h
  cases h with
  | nil => intro x y t' hr; exact absurd hr (by simp)
  | @cons b t₂ x' y' r' hc hk =>
      intro x y t' hr
      cases hr
      exact ⟨b, t₂, rfl, hc, hk⟩

/-- Every trace is chunked by itself, one pair per singleton block. -/
theorem Chunk.refl (t : Trace (S × S)) : Chunk t t := by
  induction t with
  | nil => exact .nil
  | cons e t ih =>
      obtain ⟨x, y⟩ := e
      exact Chunk.cons (b := [(x, y)]) (.cons x y (.nil y)) ih

/-! ## `Chunk` is stutter/mumble refinement -/

/-- An interference-free execution refines to the single pair of its endpoints:
mumble it all the way down. -/
theorem Chain.refines_single {s : S} {t : Trace (S × S)} {s' : S} (h : Chain s t s') :
    (rewriting S).Refines t [(s, s')] := by
  induction h with
  | nil s => exact .single (Step.stutter s [])
  | cons s m _ ih =>
      exact ((rewriting S).refines_appendLeft [(s, m)] ih).tail (Step.mumble s m _ [])

/-- Chunking implies refinement. -/
theorem Chunk.refines {t t' : Trace (S × S)} (h : Chunk t t') :
    (rewriting S).Refines t t' := by
  induction h with
  | nil => exact .refl
  | cons hc _ ih => exact Rewriting.refines_append hc.refines_single ih

/-- Chunking absorbs a rewriting step on the right. -/
theorem Chunk.step {t t' t'' : Trace (S × S)} (h : Chunk t t') (hs : Step S t' t'') :
    Chunk t t'' := by
  induction hs generalizing t with
  | stutter μ r => exact Chunk.cons (b := []) (.nil μ) h
  | mumble μ ρ θ r =>
      obtain ⟨b₁, t₂, rfl, hc₁, hk₁⟩ := h.cons_inv rfl
      obtain ⟨b₂, t₃, rfl, hc₂, hk₂⟩ := hk₁.cons_inv rfl
      rw [← List.append_assoc]
      exact Chunk.cons (hc₁.append hc₂) hk₂
  | cons p _ ih =>
      obtain ⟨x, y⟩ := p
      obtain ⟨b, t₂, rfl, hc, hk⟩ := h.cons_inv rfl
      exact Chunk.cons hc (ih hk)

/-- **`Chunk` is exactly stutter/mumble refinement.**  An empty block is a
stutter; a block of length ≥ 2 is iterated mumbling. -/
theorem chunk_iff_refines {t t' : Trace (S × S)} :
    Chunk t t' ↔ (rewriting S).Refines t t' := by
  constructor
  · exact Chunk.refines
  · intro h
    induction h with
    | refl => exact Chunk.refl t
    | tail _ hs ih => exact ih.step hs

/-- Refining down to a single pair is exactly being an interference-free
execution between its two states. -/
theorem chain_iff_refines_single {s s' : S} {t : Trace (S × S)} :
    Chain s t s' ↔ (rewriting S).Refines t [(s, s')] := by
  constructor
  · exact Chain.refines_single
  · intro h
    obtain ⟨b, t₂, rfl, hc, hk⟩ := (chunk_iff_refines.2 h).cons_inv rfl
    rw [hk.nil_inv rfl, List.append_nil]
    exact hc

/-! ## Reconstructing a trace from its interruptions

`zip s u s'` is the trace whose *interruptions* are the pairs of `u`: it starts
at `s`, ends at `s'`, and between consecutive pairs of `u` leaves exactly the
gaps `u` fills.  It is inverse to Brookes's `α ↦ ᾱ`. -/

/-- `zip s u s'`: the trace with initial rely `s`, final guarantee `s'`, and
interruptions `u`. -/
def zip : S → Trace (S × S) → S → Trace (S × S)
  | s, [], s' => [(s, s')]
  | s, (a, b) :: u, s' => (s, a) :: zip b u s'

@[simp] theorem zip_nil (s s' : S) : zip s [] s' = [(s, s')] := rfl

@[simp] theorem zip_cons (s a b : S) (u : Trace (S × S)) (s' : S) :
    zip s ((a, b) :: u) s' = (s, a) :: zip b u s' := rfl

/-- The initial state of `zip` is a parameter the rest of the trace does not
depend on. -/
theorem zip_eq_cons (u : Trace (S × S)) (s' : S) :
    ∃ (x : S) (r : Trace (S × S)), ∀ m : S, zip m u s' = (m, x) :: r := by
  cases u with
  | nil => exact ⟨s', [], fun _ ↦ rfl⟩
  | cons p u => obtain ⟨a, b⟩ := p; exact ⟨a, zip b u s', fun _ ↦ rfl⟩

/-- `merge s u s'`: the alternating shuffle of `zip s u s'` with `u`, which is
the interference-free run Brookes uses in the positive half of the definability
argument. -/
def merge : S → Trace (S × S) → S → Trace (S × S)
  | s, [], s' => [(s, s')]
  | s, (a, b) :: u, s' => (s, a) :: (a, b) :: merge b u s'

/-- `merge` really is a shuffle of `zip` with the interruptions. -/
theorem interleave_zip_merge (s : S) (u : Trace (S × S)) (s' : S) :
    Interleave (zip s u s') u (merge s u s') := by
  induction u generalizing s with
  | nil => exact Interleave.left .nil
  | cons p u ih => obtain ⟨a, b⟩ := p; exact Interleave.left (Interleave.right (ih b))

/-- The alternating shuffle is interference-free from `s` to `s'`. -/
theorem chain_merge (s : S) (u : Trace (S × S)) (s' : S) : Chain s (merge s u s') s' := by
  induction u generalizing s with
  | nil => exact .cons s s' (.nil s')
  | cons p u ih => obtain ⟨a, b⟩ := p; exact .cons s a (.cons a b (ih b))

/-! ## The Key Lemma -/

/-- **Key Lemma.**  If a shuffle of `t` with `u` is an interference-free
execution from `s` to `s'`, then cutting it at the `u`-pairs exhibits `t` as a
chunking of `zip s u s'`; equivalently, `t` refines to `zip s u s'`.

This is the step Brookes dismisses as "easy to see" (journal p. 152).  The two
shuffle constructors read as: a left step extends the current block by one pair,
a right step closes the current block and opens an empty one. -/
theorem chunk_of_interleave_chain : ∀ {t u w : Trace (S × S)}, Interleave t u w →
    ∀ {s s' : S}, Chain s w s' → Chunk t (zip s u s') := by
  intro t u w hi
  induction hi with
  | nil => intro s s' hc; cases hc; exact Chunk.cons (b := []) (.nil s) .nil
  | @left e t u w _ ih =>
      intro s s' hc
      obtain ⟨e₁, e₂⟩ := e
      obtain ⟨rfl, hc'⟩ := hc.cons_inv rfl
      obtain ⟨x, r, hz⟩ := zip_eq_cons u s'
      have hih := ih hc'
      rw [hz e₂] at hih
      obtain ⟨b, t₂, rfl, hcb, hk⟩ := hih.cons_inv rfl
      rw [hz e₁]
      exact Chunk.cons (b := (e₁, e₂) :: b) (.cons e₁ e₂ hcb) hk
  | @right e t u w _ ih =>
      intro s s' hc
      obtain ⟨e₁, e₂⟩ := e
      obtain ⟨rfl, hc'⟩ := hc.cons_inv rfl
      exact Chunk.cons (b := []) (.nil e₁) (ih hc')

/-! ## Contravariance of `zip`

Closing the trace set of the separating context makes its *interruptions*
coarser, hence the reconstructed trace finer.  This is what absorbs the closure
operator in `T[DO_α]`. -/

/-- One rewriting step of the interruptions reverses under `zip`: a stutter
becomes a mumble and a mumble becomes a stutter. -/
theorem zip_refines_step : ∀ {u u' : Trace (S × S)}, Step S u u' →
    ∀ s s' : S, (rewriting S).Refines (zip s u' s') (zip s u s') := by
  intro u u' h
  induction h with
  | stutter μ r =>
      intro s s'
      obtain ⟨x, q, hz⟩ := zip_eq_cons r s'
      rw [zip_cons, hz μ, hz s]
      exact .single (Step.mumble s μ x q)
  | mumble μ ρ θ r =>
      intro s s'
      rw [zip_cons, zip_cons, zip_cons]
      exact .single (Step.cons (s, μ) (Step.stutter ρ (zip θ r s')))
  | cons p _ ih =>
      intro s s'
      obtain ⟨a, b⟩ := p
      rw [zip_cons, zip_cons]
      exact (rewriting S).refines_appendLeft [(s, a)] (ih b s')

/-- Refinement of the interruptions reverses under `zip`. -/
theorem zip_refines {u u' : Trace (S × S)} (h : (rewriting S).Refines u u') (s s' : S) :
    (rewriting S).Refines (zip s u' s') (zip s u s') := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact (zip_refines_step hs s s').trans ih

/-- **The separating-context lemma, semantic half.**  If some shuffle of `t`
with a refinement `β` of `u` collapses to the single pair `(s, s')`, then `t`
already refines to `zip s u s'`.

Together with closure of trace sets this is exactly Brookes's negative
direction: no command can be run against `DO_α` to yield `(s₀, s_k')` unless it
already has the trace `α`. -/
theorem refines_zip_of_interleave {t β w u : Trace (S × S)} {s s' : S}
    (hi : Interleave t β w) (hβ : (rewriting S).Refines u β)
    (hw : (rewriting S).Refines w [(s, s')]) :
    (rewriting S).Refines t (zip s u s') :=
  ((chunk_of_interleave_chain hi (chain_iff_refines_single.2 hw)).refines).trans
    (zip_refines hβ s s')

end SeqCst

end Isotope.Elgot.Brookes
