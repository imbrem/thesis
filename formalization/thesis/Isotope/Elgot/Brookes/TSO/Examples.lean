import Isotope.Elgot.Brookes.TSO.Litmus

/-!
# What the operations do, and what a fence is for

Everything here is stated about *interference-free* executions (`Seq`), which is
what makes the statements sharp: a Brookes computation on its own always allows
arbitrary environment steps, so "the final memory is …" is only meaningful once
the environment is fixed to do nothing.  Every statement is about the **closed**
trace set, not about the generators, because `Seq.of_refines` lets stuttering and
mumbling be undone.

The pair to compare is:

* `writeCore_invisible` — a TSO write changes no global memory at all; it only
  grows the issuing thread's buffer.  That single fact is store buffering.
* `writeSC_visible` — a sequentially consistent write updates memory at once.
* `writeCore_fence_commits` — after a fence, the buffered write *has* reached
  memory and the buffer is empty.  A fence buys back exactly what buffering gave
  away.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace TSO

variable {Tid Loc Val : Type u} [DecidableEq Tid] [DecidableEq Loc]

omit [DecidableEq Tid] [DecidableEq Loc] in
/-- An interference-free execution of a concatenation splits at the seam. -/
theorem Seq.append_split :
    ∀ {u v : Tr Tid Loc Val} {s sf : St Tid Loc Val}, Seq s (u ++ v) sf →
      ∃ m, Seq s u m ∧ Seq m v sf := by
  intro u
  induction u with
  | nil => intro v s sf h; exact ⟨s, .nil, h⟩
  | cons p u ih =>
    intro v s sf h
    obtain ⟨q, q'⟩ := p
    cases h with
    | cons h' =>
      obtain ⟨m, h₁, h₂⟩ := ih h'
      exact ⟨m, .cons h₁, h₂⟩

/-! ## The single-step operations -/

omit [DecidableEq Loc] in
/-- Issuing a TSO write appends to the issuing thread's buffer and does nothing else. -/
theorem seq_of_mem_writeCore {i : Tid} {ℓ : Loc} {v : Val} {t : Tr Tid Loc Val}
    {a : PUnit} {s sf : St Tid Loc Val} (h : (t, a) ∈ writeCore i ℓ v) (hs : Seq s t sf) :
    sf = s.push i ℓ v := by
  obtain ⟨t₀, ⟨s₀, ht₀⟩, hr⟩ := h
  have hseq := Seq.of_refines hr hs
  rw [show t₀ = [(s₀, s₀.push i ℓ v)] from ht₀] at hseq
  cases hseq with | cons h' => exact (Seq.nil_eq h').symm

omit [DecidableEq Loc] in
/-- **A TSO write is invisible in global memory.**  This is store buffering in one
line: nothing another thread can read has changed. -/
theorem writeCore_invisible {i : Tid} {ℓ : Loc} {v : Val} {t : Tr Tid Loc Val}
    {a : PUnit} {s sf : St Tid Loc Val} (h : (t, a) ∈ writeCore i ℓ v) (hs : Seq s t sf) :
    sf.mem = s.mem := by rw [seq_of_mem_writeCore h hs]; rfl

omit [DecidableEq Loc] in
/-- After issuing a TSO write, it is the last entry of the issuing thread's buffer. -/
theorem writeCore_buf {i : Tid} {ℓ : Loc} {v : Val} {t : Tr Tid Loc Val}
    {a : PUnit} {s sf : St Tid Loc Val} (h : (t, a) ∈ writeCore i ℓ v) (hs : Seq s t sf) :
    sf.buf i = s.buf i ++ [(ℓ, v)] := by
  rw [seq_of_mem_writeCore h hs, St.buf_push, Function.update_self]

omit [DecidableEq Tid] in
/-- **A sequentially consistent write is visible at once.** -/
theorem writeSC_visible {ℓ : Loc} {v : Val} {t : Tr Tid Loc Val} {a : PUnit}
    {s sf : St Tid Loc Val} (h : (t, a) ∈ (writeSC ℓ v : Comp Tid Loc Val PUnit))
    (hs : Seq s t sf) : sf.mem = Function.update s.mem ℓ v := by
  obtain ⟨t₀, ⟨s₀, ht₀⟩, hr⟩ := h
  have hseq := Seq.of_refines hr hs
  rw [show t₀ = [(s₀, s₀.setMem ℓ v)] from ht₀] at hseq
  cases hseq with | cons h' => rw [← Seq.nil_eq h']; rfl

/-- Consequently the two writes are different computations whenever the write
actually changes memory somewhere. -/
theorem writeCore_ne_writeSC {i : Tid} {ℓ : Loc} {v : Val} {s : St Tid Loc Val}
    (hne : Function.update s.mem ℓ v ≠ s.mem) :
    (writeCore i ℓ v : Comp Tid Loc Val PUnit) ≠ writeSC ℓ v := by
  intro heq
  have hmem : (([(s, s.setMem ℓ v)] : Tr Tid Loc Val), PUnit.unit) ∈ writeCore i ℓ v := by
    rw [heq]; exact mem_writeSC ℓ v s PUnit.unit
  exact hne (writeCore_invisible hmem (.cons .nil))

omit [DecidableEq Tid] in
/-- A TSO read observes the issuing thread's buffer if it can, and memory otherwise. -/
theorem seq_of_mem_readCore {i : Tid} {ℓ : Loc} {t : Tr Tid Loc Val} {r : Val}
    {s sf : St Tid Loc Val} (h : (t, r) ∈ readCore i ℓ) (hs : Seq s t sf) :
    r = s.observe i ℓ ∧ sf = s := by
  obtain ⟨t₀, ⟨s₀, ht₀, hr₀⟩, hr⟩ := h
  have hseq := Seq.of_refines hr hs
  rw [show t₀ = [(s₀, s₀)] from ht₀] at hseq
  cases hseq with
  | cons h' => exact ⟨hr₀, (Seq.nil_eq h').symm⟩

/-! ## Fences -/

/-- A fence leaves the issuing thread's buffer empty. -/
theorem Fences.seq_buf_nil {i : Tid} {t : Tr Tid Loc Val} (h : Fences i t) :
    ∀ {s sf : St Tid Loc Val}, Seq s t sf → sf.buf i = [] := by
  induction h with
  | done hb => intro s sf hs; cases hs with | cons h' => rw [← Seq.nil_eq h']; exact hb
  | step _ _ ih => intro s sf hs; cases hs with | cons h' => exact ih h'

/-- A fence from an already-empty buffer changes nothing in memory. -/
theorem Fences.seq_mem_of_buf_nil {i : Tid} {t : Tr Tid Loc Val} (h : Fences i t) :
    ∀ {s sf : St Tid Loc Val}, Seq s t sf → s.buf i = [] → sf.mem = s.mem := by
  induction h with
  | done _ => intro s sf hs _; cases hs with | cons h' => rw [← Seq.nil_eq h']
  | step hf _ ih =>
    intro s sf hs hb
    cases hs with | cons _ => exact absurd hb hf.buf_ne_nil

/-- **A fence publishes the last buffered write.**  If the issuing thread's buffer
ends with `ℓ := v`, then after the fence global memory holds `v` at `ℓ`. -/
theorem Fences.seq_commits_last {i : Tid} {t : Tr Tid Loc Val} (h : Fences i t) :
    ∀ {s sf : St Tid Loc Val} {β : Buf Loc Val} {ℓ : Loc} {v : Val},
      Seq s t sf → s.buf i = β ++ [(ℓ, v)] → sf.mem ℓ = v := by
  induction h with
  | done hb =>
    intro s sf β ℓ v hs hbuf
    cases hs with
    | cons _ =>
      rw [hb] at hbuf
      exact absurd hbuf.symm (List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _))
  | @step u u' t' hf ht ih =>
    intro s sf β ℓ v hs hbuf
    cases hs with
    | cons hs' =>
      obtain ⟨k, w, γ, hk, rfl⟩ := hf
      rw [hk] at hbuf
      cases β with
      | nil =>
        rw [List.nil_append, List.cons.injEq] at hbuf
        obtain ⟨hkw, hγ⟩ := hbuf
        injection hkw with hk' hw'
        subst hk'
        subst hw'
        subst hγ
        rw [ht.seq_mem_of_buf_nil hs' (by simp)]
        exact Function.update_self _ _ _
      | cons p β' =>
        rw [List.cons_append, List.cons.injEq] at hbuf
        refine ih (β := β') hs' ?_
        simpa using hbuf.2

/-- Every interference-free execution of a fence drains the issuing thread's buffer. -/
theorem fence_drains {i : Tid} {t : Tr Tid Loc Val} {a : PUnit} {s sf : St Tid Loc Val}
    (h : (t, a) ∈ fence i) (hs : Seq s t sf) : sf.buf i = [] := by
  obtain ⟨t₀, ht₀, hr⟩ := h
  exact ht₀.seq_buf_nil (Seq.of_refines hr hs)

/-- Every interference-free execution of a fence publishes the last buffered write. -/
theorem fence_commits {i : Tid} {t : Tr Tid Loc Val} {a : PUnit} {s sf : St Tid Loc Val}
    {β : Buf Loc Val} {ℓ : Loc} {v : Val} (h : (t, a) ∈ fence i) (hs : Seq s t sf)
    (hb : s.buf i = β ++ [(ℓ, v)]) : sf.mem ℓ = v := by
  obtain ⟨t₀, ht₀, hr⟩ := h
  exact ht₀.seq_commits_last (Seq.of_refines hr hs) hb

/-- **A fence restores visibility.**  Issuing a TSO write and then fencing leaves
the write in global memory and the buffer empty — the exact opposite of
`writeCore_invisible`. -/
theorem writeCore_fence_commits {i : Tid} {ℓ : Loc} {v : Val} {t : Tr Tid Loc Val}
    {a : PUnit} {s sf : St Tid Loc Val}
    (h : (t, a) ∈ (writeCore i ℓ v >>= fun _ ↦ fence i : Comp Tid Loc Val PUnit))
    (hs : Seq s t sf) : sf.mem ℓ = v ∧ sf.buf i = [] := by
  obtain ⟨b, u₁, v₁, h₁, h₂, hr⟩ := (Brookes.mem_bind_iff _ _ _ _).1 h
  obtain ⟨m, hm₁, hm₂⟩ := Seq.append_split (Seq.of_refines hr hs)
  exact ⟨fence_commits h₂ hm₂ (writeCore_buf h₁ hm₁), fence_drains h₂ hm₂⟩

end TSO

end Isotope.Elgot.Brookes
