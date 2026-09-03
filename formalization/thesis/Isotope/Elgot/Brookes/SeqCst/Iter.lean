import Isotope.Elgot.Brookes.SeqCst.Laws

/-!
# `while` as an Elgot iterate

Brookes defines the trace semantics of `while B do C` by the Kleene star,
`den (while B do C) = (test B ; den C)* ; test ¬B`, and never mentions a fixed
point combinator.  The lambda-iter and SSA semantics of this development, by
contrast, interpret loops and back-edges with `Elgot.iter` — the approximant
union `f† = ⋃ᵢ fᵢ` of `Brookes/Iteration.lean`.

This file proves the two presentations agree, at the level of computations:

* `iter_eq_star` : `iter (whileBody z w) ⋆ = z* ; w`, for *arbitrary* unit-valued
  `z` and `w` — no reference to the syntax of commands;
* `den_wh_eq_iter` : the instance at `z := test B ; den C`, `w := test ¬B`,
  which is exactly `den (while B do C)`.

The loop body `whileBody z w` is the evident coproduct-valued step: it either
runs `z` and asks to go round again (`Sum.inr`), or runs `w` and stops
(`Sum.inl`).  The proof is by matching approximants: `Brookes.approx` at stage
`n` is exactly the union of the first `n` powers of `z`, postcomposed with `w`
(`approx_whileBody`), and both `star` and `iterate` are unions over `Nat`, so no
closure or trace-level reasoning is needed anywhere.

`union2` of `Brookes/SeqCst/Syntax.lean` is `PUnit`-specific, but the loop body
is valued in `PUnit ⊕ PUnit`, so the generic binary union `union2'` is
introduced here; `union2'_eq_union2` says it is literally the same definition at
`PUnit`, so every `union2` law of `Laws.lean` transfers by `rfl`.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {Loc Val : Type u}

/-! ## Binary union at an arbitrary result type -/

/-- Binary nondeterministic choice, at an arbitrary result type.  This is
`union2` with the `PUnit` restriction lifted; the loop body below is valued in
`PUnit ⊕ PUnit`, so it does not fit `union2`. -/
def union2' {A : Type u} (x y : Comp Loc Val A) : Comp Loc Val A :=
  Brookes.iUnion fun b : Bool ↦ cond b x y

@[simp] theorem mem_union2'_iff {A : Type u} {x y : Comp Loc Val A}
    {p : Trace (Store Loc Val × Store Loc Val) × A} :
    p ∈ union2' x y ↔ p ∈ x ∨ p ∈ y := by
  rw [union2', Brookes.mem_iUnion_iff]
  constructor
  · rintro ⟨b, hb⟩; cases b
    · exact Or.inr hb
    · exact Or.inl hb
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩

/-- At `PUnit`, `union2'` is `union2` on the nose, so every law of `union2` in
`Brookes/SeqCst/Laws.lean` applies to it. -/
theorem union2'_eq_union2 (x y : Comp Loc Val PUnit) : union2' x y = union2 x y := rfl

/-- `union2'` distributes over `bind` on the left, as `union2_bind` does. -/
theorem union2'_bind {A B : Type u} (x y : Comp Loc Val A) (f : A → Comp Loc Val B) :
    (union2' x y >>= f) = union2' (x >>= f) (y >>= f) := by
  apply ext_mem
  intro t a
  rw [mem_bind_iff, mem_union2'_iff, mem_bind_iff, mem_bind_iff]
  constructor
  · rintro ⟨b, u, v, hu, hv, hr⟩
    rcases mem_union2'_iff.1 hu with h | h
    · exact Or.inl ⟨b, u, v, h, hv, hr⟩
    · exact Or.inr ⟨b, u, v, h, hv, hr⟩
  · rintro (⟨b, u, v, hu, hv, hr⟩ | ⟨b, u, v, hu, hv, hr⟩)
    · exact ⟨b, u, v, mem_union2'_iff.2 (Or.inl hu), hv, hr⟩
    · exact ⟨b, u, v, mem_union2'_iff.2 (Or.inr hu), hv, hr⟩

/-! ## Finite unions -/

/-- The empty finite union is `⊥`. -/
theorem iUnion_fin_zero {A : Type u} (F : Nat → Comp Loc Val A) :
    Brookes.iUnion (fun k : Fin 0 ↦ F k.val) = ⊥ := by
  apply ext_mem
  intro t a
  rw [Brookes.mem_iUnion_iff]
  exact ⟨fun ⟨k, _⟩ ↦ absurd k.isLt (by omega), fun h ↦ h.elim⟩

/-- A finite union of `n + 1` terms peels off its *first* term, leaving the
remaining `n` shifted up by one.  This is the orientation the approximant
induction needs, since `approx` unfolds `f` at the front. -/
theorem iUnion_fin_succ {A : Type u} (F : Nat → Comp Loc Val A) (n : Nat) :
    Brookes.iUnion (fun k : Fin (n+1) ↦ F k.val)
      = union2' (Brookes.iUnion (fun k : Fin n ↦ F (k.val + 1))) (F 0) := by
  apply ext_mem
  intro t a
  rw [Brookes.mem_iUnion_iff, mem_union2'_iff, Brookes.mem_iUnion_iff]
  constructor
  · rintro ⟨⟨k, hk⟩, h⟩
    cases k with
    | zero => exact Or.inr h
    | succ k => exact Or.inl ⟨⟨k, by omega⟩, h⟩
  · rintro (⟨⟨k, hk⟩, h⟩ | h)
    · exact ⟨⟨k+1, by omega⟩, h⟩
    · exact ⟨⟨0, by omega⟩, h⟩

/-! ## The loop body -/

/-- The Elgot loop body for `while`: either run `z` and go round again
(`Sum.inr`), or run `w` and stop (`Sum.inl`).  (It is `whileBody`, not
`loopBody`: that name is taken by the concrete two-state example loop of
`Brookes/Examples.lean`.)

The `PUnit.{u+1}` annotations are not decoration: `Comp Loc Val A` forces
`A : Type u`, and an unannotated `PUnit ⊕ PUnit` leaves Lean solving
`u =?= max ?v ?w`, which it cannot. -/
def whileBody (z w : Comp Loc Val PUnit) :
    PUnit.{u+1} → Comp Loc Val (PUnit.{u+1} ⊕ PUnit.{u+1}) :=
  fun _ ↦ union2' (z >>= fun _ ↦ pure (Sum.inr PUnit.unit))
                  (w >>= fun _ ↦ pure (Sum.inl PUnit.unit))

theorem bind_power_succ (z w : Comp Loc Val PUnit) (k : Nat) :
    (z >>= fun _ ↦ (power z k >>= fun _ ↦ w)) = (power z (k+1) >>= fun _ ↦ w) := by
  rw [power_succ, bind_assoc_eq]

/-- The `n`-th approximant of the loop is exactly "at most `n-1` iterations of
`z`, then `w`" — the first `n` powers of `z`, postcomposed with `w`. -/
theorem approx_whileBody (z w : Comp Loc Val PUnit) : ∀ n : Nat,
    Brookes.approx (whileBody z w) n PUnit.unit
      = Brookes.iUnion (fun k : Fin n ↦ power z k.val) >>= fun _ ↦ w := by
  intro n
  induction n with
  | zero => rw [Brookes.approx_zero, iUnion_fin_zero, bot_bind]
  | succ n ih =>
    rw [Brookes.approx_succ, whileBody, union2'_bind, bind_assoc_eq, bind_assoc_eq]
    have h1 : (z >>= fun _ ↦ ((pure (Sum.inr PUnit.unit) : Comp Loc Val (PUnit.{u+1} ⊕ PUnit.{u+1}))
        >>= Sum.elim pure (Brookes.approx (whileBody z w) n)))
        = (z >>= fun _ ↦ (Brookes.iUnion (fun k : Fin n ↦ power z k.val) >>= fun _ ↦ w)) := by
      congr 1; funext _; rw [pure_bind_eq]; exact ih
    have h2 : (w >>= fun _ ↦ ((pure (Sum.inl PUnit.unit) : Comp Loc Val (PUnit.{u+1} ⊕ PUnit.{u+1}))
        >>= Sum.elim pure (Brookes.approx (whileBody z w) n))) = w := by
      have : (w >>= fun _ ↦ ((pure (Sum.inl PUnit.unit) : Comp Loc Val (PUnit.{u+1} ⊕ PUnit.{u+1}))
          >>= Sum.elim pure (Brookes.approx (whileBody z w) n)))
          = (w >>= fun a ↦ pure a) := by
        congr 1; funext _; rw [pure_bind_eq]; rfl
      rw [this, bind_pure_eq]
    rw [h1, h2, iUnion_fin_succ, union2'_bind, Brookes.iUnion_bind, Brookes.iUnion_bind,
      Brookes.bind_iUnion]
    congr 1
    · congr 1; funext k; exact bind_power_succ z w k.val
    · rw [power_zero, pure_bind_eq]

/-! ## Kleene star is Elgot iteration -/

/-- **The Kleene star of `Brookes/SeqCst/Syntax.lean` is the Elgot iterate of
`Brookes/Iteration.lean`.**  Both sides are unions over `Nat`; the only content
is that the `n`-th approximant of the loop is the union of the first `n`
powers. -/
theorem iter_eq_star (z w : Comp Loc Val PUnit) :
    Elgot.iter (whileBody z w) PUnit.unit = (star z >>= fun _ ↦ w) := by
  rw [Brookes.iter_eq, Brookes.iterate, star, Brookes.iUnion_bind]
  apply ext_mem
  intro t a
  rw [Brookes.mem_iUnion_iff, Brookes.mem_iUnion_iff]
  constructor
  · rintro ⟨n, hn⟩
    rw [approx_whileBody, Brookes.iUnion_bind, Brookes.mem_iUnion_iff] at hn
    obtain ⟨k, hk⟩ := hn
    exact ⟨k.val, hk⟩
  · rintro ⟨n, hn⟩
    refine ⟨n + 1, ?_⟩
    rw [approx_whileBody, Brookes.iUnion_bind, Brookes.mem_iUnion_iff]
    exact ⟨⟨n, by omega⟩, hn⟩

/-- **`while` is an Elgot iterate.**  Brookes's star-based clause `den_wh` is
literally `Elgot.iter` applied to the evident loop body — so the imperative
`while` and the loops of the lambda-iter and SSA semantics are interpreted by
the same operation. -/
theorem den_wh_eq_iter [DecidableEq Loc] [DecidableEq Val] (b : BExp Loc Val) (C : Com Loc Val) :
    den (Com.wh b C)
      = Elgot.iter (whileBody (test b.eval >>= fun _ ↦ den C) (test (BExp.neg b).eval))
          PUnit.unit := by
  rw [den_wh, iter_eq_star]

end SeqCst

end Isotope.Elgot.Brookes
