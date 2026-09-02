import Isotope.Elgot.TSO.Validity

/-!
# Worked TSO examples

Iteration in the partial-correctness monad, and the store-buffering behaviour of `write`
against the draining behaviour of `fence`.

## Honest boundary

There is **no fork-join parallel composition of morphisms** here (the paper's L4790-4804 and
L4868-4880 are not formalised), so the two-thread store-buffering litmus is *not* proved.
What is proved is the single-thread mechanism that produces it: a write may remain in the
buffer after `write_x` returns, so it is not yet globally visible, and a following `fence`
forces the buffer empty.  Exclusion of the litmus outcome would additionally require the
validity post-filter of L4781-4788, which is not formalised.
-/

universe u

namespace Isotope.Elgot.TSO

open Isotope.Pomset Isotope.Elgot

variable {Loc Val : Type u} {A B : Type u}

section Iteration

theorem mem_pure_value {C : Type u} {c : C} {L : Buf Loc Val}
    {e : Exec (Buf Loc Val) (Pom (Act Loc Val)) C}
    (h : e ∈ (pure c : TSO Loc Val C).runs L) : e = ⟨c, L, 1⟩ := h

/-- A body that returns immediately: the loop is its body. -/
theorem iter_immediate (a : A) (b : B) :
    iter (fun _ : A ↦ (pure (Sum.inl b) : TSO Loc Val (B ⊕ A))) a = pure b := by
  ext L e
  rw [WS.mem_iter_iff]
  obtain ⟨v, s, w⟩ := e
  constructor
  · intro h
    cases h with
    | done hs =>
        have hs' : (⟨Sum.inl v, s, w⟩ : Exec (Buf Loc Val) (Pom (Act Loc Val)) (B ⊕ A)) =
            ⟨Sum.inl b, L, 1⟩ := hs
        simp only [Exec.mk.injEq, Sum.inl.injEq] at hs'
        obtain ⟨rfl, rfl, rfl⟩ := hs'
        rfl
    | more hs _ =>
        rename_i a' t w' _ _
        have hs' : (⟨Sum.inr a', t, w'⟩ : Exec (Buf Loc Val) (Pom (Act Loc Val)) (B ⊕ A)) =
            ⟨Sum.inl b, L, 1⟩ := hs
        simp only [Exec.mk.injEq] at hs'
        exact absurd hs'.1 (by simp)
  · intro h
    have h' : (⟨v, s, w⟩ : Exec (Buf Loc Val) (Pom (Act Loc Val)) B) = ⟨b, L, 1⟩ := h
    simp only [Exec.mk.injEq] at h'
    obtain ⟨rfl, rfl, rfl⟩ := h'
    exact .done rfl

/-- **A body that always recurses denotes no execution at all.**  This is the honest face of
partial correctness: divergence is indistinguishable from failure in `WS`. -/
theorem iter_forever (a : A) (L : Buf Loc Val) :
    (iter (fun a' : A ↦ (pure (Sum.inr a') : TSO Loc Val (B ⊕ A))) a).runs L = ∅ := by
  ext e
  obtain ⟨b, s, w⟩ := e
  simp only [Set.mem_empty_iff_false, iff_false, WS.mem_iter_iff]
  intro h
  induction h with
  | done hs => exact absurd (congrArg Exec.value (mem_pure_value hs)) (by simp)
  | more _ _ ih => exact ih

end Iteration

section StoreBuffering

variable (x : Loc) (v : Val)

/-- **The store-buffering behaviour is admitted.**  Starting from an empty buffer, `write_x v`
has an execution that leaves `b(x) := v` sitting in the buffer: the write has been emitted as
a program-order event but has not yet been flushed, so it is not visible to other threads. -/
theorem write_stays_buffered :
    (⟨⟨⟩, [(x, v)], Pom.mk (PrePom.single (Act.write x v))⟩ :
        Exec (Buf Loc Val) (Pom (Act Loc Val)) PUnit) ∈ (write x v).runs [] := by
  refine ⟨⟨v, [], Buf.toPom []⟩, ⟨[], [], rfl, rfl⟩,
    ⟨⟨⟩, [(x, v)], Pom.mk (PrePom.single (Act.write x v)) * Buf.toPom []⟩,
    ⟨⟨⟨⟩, [(x, v)], Pom.mk (PrePom.single (Act.write x v))⟩, rfl,
      ⟨⟨⟩, [(x, v)], Buf.toPom []⟩, ⟨[], [(x, v)], rfl, rfl⟩, rfl⟩, ?_⟩
  simp

/-- Consequently `write_x` does **not** always drain its buffer. -/
theorem write_not_always_drained :
    ¬ ∀ e ∈ (write (Loc := Loc) (Val := Val) x v).runs [], e.state = [] := by
  intro h
  exact absurd (h _ (write_stays_buffered x v)) (by simp)

/-- **A fence drains.**  Every execution of a computation followed by `fence` ends with an
empty buffer, so every buffered write has been emitted into the pomset before the fence. -/
theorem bind_fence_state (c : TSO Loc Val PUnit) (L : Buf Loc Val)
    (e : Exec (Buf Loc Val) (Pom (Act Loc Val)) PUnit)
    (h : e ∈ (c >>= fence).runs L) : e.state = [] := by
  obtain ⟨r₁, _, r₂, h₂, rfl⟩ := h
  have h₂' : r₂ = ⟨⟨⟩, [], Buf.toPom r₁.state⟩ := h₂
  subst h₂'
  rfl

/-- The fenced write always drains, while the unfenced one need not: this is exactly the
buffer-state distinction that a fence buys in this model. -/
theorem write_fence_drained (L : Buf Loc Val) :
    ∀ e ∈ (write (Loc := Loc) (Val := Val) x v >>= fence).runs L, e.state = [] :=
  fun e he => bind_fence_state _ L e he

end StoreBuffering

section Reads

variable [DecidableEq Loc] (x : Loc)

/-- **A read on a buffer miss returns an arbitrary value**, faithful to L4845: there is no
global memory in this model, so nothing constrains the value read. -/
theorem read_admits_any_value (v : Val) :
    ∃ e ∈ (read (Loc := Loc) (Val := Val) x ⟨⟩).runs [], e.value = v := by
  refine ⟨⟨v, [], Buf.toPom [] * (Pom.mk (PrePom.single (Act.read x v)) * Buf.toPom [])⟩,
    ⟨⟨⟨⟩, [], Buf.toPom []⟩, ⟨[], [], rfl, rfl⟩,
      ⟨v, [], Pom.mk (PrePom.single (Act.read x v)) * Buf.toPom []⟩,
      ⟨⟨v, [], Pom.mk (PrePom.single (Act.read x v))⟩, ⟨v, Or.inr rfl, rfl⟩,
        ⟨v, [], Buf.toPom []⟩, ⟨[], [], rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩

end Reads

end Isotope.Elgot.TSO
