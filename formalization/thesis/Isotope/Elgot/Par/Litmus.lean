import Isotope.Elgot.Par.Brookes
import Isotope.Elgot.Par.Pomset
import Isotope.Elgot.TSO

/-!
# A litmus separation: sequential consistency against the pomset TSO model

The headline comparison of this track, stated for what it is: a **litmus separation**, not an
inclusion of models.  The Brookes model of sequential consistency
(`Isotope/Elgot/Brookes/SeqCst.lean`) and the SPARC pomset TSO model
(`Isotope/Elgot/TSO/`) have different state types, different trace shapes and different
monads, so no inclusion of denotations typechecks.  What can be compared is a *program
pattern* and an *outcome*, in the style of `sc_forbids_store_buffering` /
`tso_admits_store_buffering` of `Isotope/Elgot/Brookes/TSO/Litmus.lean`.

## The litmus

    x := v ; read x

one thread, no concurrency at all.

* **Sequential consistency pins the value.**  In every *interference-free* execution the read
  returns `v` (`sc_read_after_write`).  Interference-freedom is essential: a Brookes trace
  deliberately allows the environment to change the state between two steps, and with
  interference any value may be read.
* **The pomset TSO model admits every value** (`pomsetTSO_read_after_write_any`), from the
  empty buffer, with no environment at all.  The reason is not weak memory: it is that the
  transcribed `readCore` returns an *arbitrary* value on a buffer miss
  (`Isotope/Elgot/TSO/Ops.lean`, faithful to L4845), the buffered write can be flushed by the
  `pflush` that opens the read, and the paper's TSO post-filter (L4781-4788) — the condition
  that would discard the incoherent executions — is not formalised anywhere.

So `pomsetTSO_strictly_richer` is honest about its own content: it says the pomset model
admits an outcome sequential consistency forbids, *at this litmus*.  It is **not** a general
"strictly fewer behaviours" theorem, and it is not evidence that the paper's TSO model is
weaker than sequential consistency in the way store buffering is; it is evidence that the
model as transcribed is missing its post-filter.

## Interference-free executions

`Seq` is the generic form of `Isotope.Elgot.Brookes.TSO.Seq`, which is stated only at the
store-buffer state `St Tid Loc Val`.  Both it and `Seq.of_refines` are proved here for an
arbitrary state type, so that the sequentially consistent model can use them; the proofs are
the same as the ones in `Isotope/Elgot/Brookes/TSO/Interleaving.lean`, generalised.

## What is *not* here

The sequential-consistency-versus-release/acquire separation is a separate workstream and is
deliberately not attempted here.  The sequential-consistency-versus-store-buffer-TSO
separation is already in `Isotope/Elgot/Brookes/TSO/Litmus.lean`; what this track adds to it
is that both sides of it use *one* parallel operator — `Brookes.par` at one pointwise
rewriting system — which now has associativity and both unit laws
(`Isotope/Elgot/Par/Brookes.lean`), recorded below as `TSO.par_assoc` and friends.
-/

universe u

namespace Isotope.Elgot.Par

open Isotope.Elgot Isotope.Elgot.Brookes

/-! ## Interference-free executions, for an arbitrary state -/

/-- `Seq s t s'`: the trace `t` is a complete execution from `s` to `s'` with no environment
interference — every gap between successive rely-guarantee pairs is closed.  The generic form
of `Isotope.Elgot.Brookes.TSO.Seq`. -/
inductive Seq {S : Type u} : S → Trace (S × S) → S → Prop
  | /-- The empty execution. -/
    nil {s : S} : Seq s [] s
  | /-- One step, taken from the current state. -/
    cons {s s' : S} {t : Trace (S × S)} {s'' : S} : Seq s' t s'' → Seq s ((s, s') :: t) s''

namespace Seq

variable {S : Type u}

/-- An interference-free empty execution changes nothing. -/
theorem nil_inv {s s' : S} (h : Seq s ([] : Trace (S × S)) s') : s = s' := by
  cases h; rfl

/-- Inverting one step of an interference-free execution. -/
theorem cons_inv {s s' : S} {p : S × S} {t : Trace (S × S)} (h : Seq s (p :: t) s') :
    s = p.1 ∧ Seq p.2 t s' := by
  cases h with
  | cons h' => exact ⟨rfl, h'⟩

/-- Stuttering and mumbling reflect interference-free executions: if a rewrite of `t` is
interference-free, so was `t`, with the same endpoints. -/
theorem of_step {t t' : Trace (S × S)} (h : SeqCst.Step S t t') {s s' : S}
    (hs : Seq s t' s') : Seq s t s' := by
  induction h generalizing s with
  | stutter μ t => cases hs with | cons h => exact h
  | mumble μ ρ θ t => cases hs with | cons h => exact .cons (.cons h)
  | cons p _ ih =>
      obtain ⟨q, q'⟩ := p
      cases hs with | cons h => exact .cons (ih h)

/-- Refinement reflects interference-free executions. -/
theorem of_refines {t t' : Trace (S × S)} (h : (SeqCst.rewriting S).Refines t t') {s s' : S}
    (hs : Seq s t' s') : Seq s t s' := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact ih (of_step hstep hs)

end Seq

/-! ## Sequential consistency pins the value read after a write -/

variable {Loc Val : Type u}

/-- **Sequential consistency forbids a stale read.**  Every interference-free execution of
`x := v ; read x` returns `v`.

Interference-freedom cannot be dropped: Brookes `bind` deliberately allows
`⟨μ, ρ⟩⟨μ', θ⟩` with `ρ ≠ μ'`, and that discontinuity is the environment overwriting `x`. -/
theorem sc_read_after_write [DecidableEq Loc] (x : Loc) (v : Val)
    {t : Trace (SeqCst.Store Loc Val × SeqCst.Store Loc Val)} {r : Val}
    {s sf : SeqCst.Store Loc Val}
    (hmem : (t, r) ∈ (SeqCst.write x v >>= fun _ ↦ SeqCst.read x))
    (hseq : Seq s t sf) : r = v := by
  obtain ⟨a, u, w, hu, hw, hr⟩ := (Brookes.mem_bind_iff _ _ _ _).1 hmem
  obtain ⟨μ, hμ⟩ := (SeqCst.mem_write_iff x v u a).1 hu
  obtain ⟨ρ, hρ, hw'⟩ := (SeqCst.mem_read_iff x w r).1 hw
  have hraw : (SeqCst.rewriting (SeqCst.Store Loc Val)).Refines
      ([(μ, Function.update μ x v)] ++ [(ρ, ρ)]) t :=
    (Rewriting.refines_append hμ hw').trans hr
  have hseq' : Seq s ([(μ, Function.update μ x v)] ++ [(ρ, ρ)]) sf := Seq.of_refines hraw hseq
  obtain ⟨-, hseq₂⟩ := Seq.cons_inv hseq'
  obtain ⟨hmid, -⟩ := Seq.cons_inv hseq₂
  have : ρ = Function.update μ x v := hmid.symm
  rw [← hρ, this, Function.update_self]

/-! ## The pomset TSO model admits every value -/

/-- Flushing the whole buffer is an execution of `pflush`. -/
theorem mem_pflush_all {A : Type u} (a : A) (L : Isotope.Elgot.TSO.Buf Loc Val) :
    (⟨a, [], Isotope.Elgot.TSO.Buf.toPom L⟩ :
      Exec (Isotope.Elgot.TSO.Buf Loc Val) (Isotope.Pomset.Pom (Isotope.Elgot.TSO.Act Loc Val))
        A) ∈ (Isotope.Elgot.TSO.pflush a).runs L :=
  ⟨L, [], by simp, rfl⟩

/-- **The pomset TSO model admits a stale read.**  For *every* value `w` there is an
execution of `x := v ; read x` from the empty buffer that returns `w`.

Two features of the transcription conspire: the `pflush` that opens `read` may drain the
buffered write, and `readCore` on a buffer miss returns an arbitrary value (L4845).  The
paper's post-filter, which would reject this execution, is not formalised. -/
theorem pomsetTSO_read_after_write_any [DecidableEq Loc] (x : Loc) (v w : Val) :
    ∃ e ∈ ((Isotope.Elgot.TSO.write x v >>= fun _ ↦ Isotope.Elgot.TSO.read x (⟨⟩ : PUnit.{u + 1}) :
        Isotope.Elgot.TSO Loc Val Val)).runs ([] : Isotope.Elgot.TSO.Buf Loc Val),
      e.value = w := by
  classical
  obtain ⟨r₁, hr₁, hst₁⟩ := Isotope.Elgot.TSO.drainable_write x v []
  have h1 := mem_pflush_all (Loc := Loc) (Val := Val) (⟨⟩ : PUnit.{u + 1})
    ([] : Isotope.Elgot.TSO.Buf Loc Val)
  have h2 : (⟨w, [], Isotope.Pomset.Pom.mk
        (Isotope.Pomset.PrePom.single (Isotope.Elgot.TSO.Act.read x w))⟩ :
      Exec (Isotope.Elgot.TSO.Buf Loc Val)
        (Isotope.Pomset.Pom (Isotope.Elgot.TSO.Act Loc Val)) Val) ∈
      (Isotope.Elgot.TSO.readCore x (⟨⟩ : PUnit.{u + 1})).runs
        ([] : Isotope.Elgot.TSO.Buf Loc Val) :=
    ⟨w, Or.inr (Isotope.Elgot.TSO.Buf.peek_nil x), rfl⟩
  have h3 := mem_pflush_all (Loc := Loc) (Val := Val) w ([] : Isotope.Elgot.TSO.Buf Loc Val)
  have hread : (⟨w, [], Isotope.Elgot.TSO.Buf.toPom ([] : Isotope.Elgot.TSO.Buf Loc Val) *
        (Isotope.Pomset.Pom.mk
          (Isotope.Pomset.PrePom.single (Isotope.Elgot.TSO.Act.read x w)) *
          Isotope.Elgot.TSO.Buf.toPom ([] : Isotope.Elgot.TSO.Buf Loc Val))⟩ :
      Exec (Isotope.Elgot.TSO.Buf Loc Val)
        (Isotope.Pomset.Pom (Isotope.Elgot.TSO.Act Loc Val)) Val) ∈
      (Isotope.Elgot.TSO.read x (⟨⟩ : PUnit.{u + 1})).runs ([] : Isotope.Elgot.TSO.Buf Loc Val) :=
    ⟨_, h1, _, ⟨_, h2, _, h3, rfl⟩, rfl⟩
  rw [← hst₁] at hread
  exact ⟨_, ⟨r₁, hr₁, _, hread, rfl⟩, rfl⟩

/-- **The litmus separation.**  At the one-thread litmus `x := v ; read x`, the pomset TSO
model admits an outcome `w ≠ v` that sequential consistency forbids.

Named for what it is: a separation at one litmus, between two models that are not otherwise
comparable.  It is *not* a general theorem that sequential consistency has fewer behaviours
than the pomset model, and the outcome it exhibits is admitted for a reason — the missing
post-filter — that has nothing to do with weak memory. -/
theorem pomsetTSO_strictly_richer [DecidableEq Loc] (x : Loc) (v w : Val) (hw : w ≠ v) :
    (∃ e ∈ ((Isotope.Elgot.TSO.write x v >>= fun _ ↦ Isotope.Elgot.TSO.read x (⟨⟩ : PUnit.{u + 1}) :
        Isotope.Elgot.TSO Loc Val Val)).runs ([] : Isotope.Elgot.TSO.Buf Loc Val),
      e.value = w) ∧
    (∀ {t : Trace (SeqCst.Store Loc Val × SeqCst.Store Loc Val)}
      {s sf : SeqCst.Store Loc Val}, Seq s t sf →
      (t, w) ∉ (SeqCst.write x v >>= fun _ ↦ SeqCst.read x)) :=
  ⟨pomsetTSO_read_after_write_any x v w,
   fun hseq hmem ↦ hw (sc_read_after_write x v hmem hseq)⟩

/-! ## What the store-buffer TSO separation now inherits

`Isotope/Elgot/Brookes/TSO/` builds its parallel composition on the *same* `Brookes.par`, at
the rewriting system `SeqCst.rewriting (St Tid Loc Val)`, which is pointwise.  The laws of
`Isotope/Elgot/Par/Brookes.lean` therefore apply to it verbatim; they are restated here for
the record, since the store-buffering litmus is the one place in the repository where two
threads are actually run. -/

section StoreBufferTSO

variable {Tid : Type u} {A B C : Type u}

/-- Store-buffer TSO parallel composition is associative, up to the associator. -/
theorem tso_par_assoc (x : Brookes.TSO.Comp Tid Loc Val A) (y : Brookes.TSO.Comp Tid Loc Val B)
    (z : Brookes.TSO.Comp Tid Loc Val C) :
    assocRL <$> Brookes.par (Brookes.par x y) z = Brookes.par x (Brookes.par y z) :=
  par_assoc x y z

/-- The idle thread is a unit for store-buffer TSO parallel composition. -/
theorem tso_par_unit_right (x : Brookes.TSO.Comp Tid Loc Val A) :
    (Prod.fst : A × PUnit.{u + 1} → A) <$> Brookes.par x (pure PUnit.unit) = x :=
  par_unit_right x

/-- Store-buffer TSO parallel composition is symmetric. -/
theorem tso_par_swap (x : Brookes.TSO.Comp Tid Loc Val A) (y : Brookes.TSO.Comp Tid Loc Val B) :
    Prod.swap <$> Brookes.par x y = Brookes.par y x :=
  par_swap x y

end StoreBufferTSO

end Isotope.Elgot.Par
