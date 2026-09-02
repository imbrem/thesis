import Isotope.Elgot.RA.Monad
import Isotope.Elgot.Basic

/-!
# Iteration for the release/acquire trace monad

**This is not in the paper.**  Dvir, Kammar and Lahav (`release-acquire`, §4)
deliberately omit recursion and loops from `λRA`, "which we leave to future
work", because recursion in their higher-order setting would require least
upper bounds of ω-chains and powerdomains.  Everything in this file is ours.

We take the simplest possible iteration operator, the one the thesis's own
appendix uses for the Brookes monad `B_c`:

```
f₀     := λ _. ⊥        f_{i+1} := f ; [id, f_i]        f† := ⋃_i f_i
```

Divergent executions contribute nothing: an always-diverging computation
denotes `∅`.  This is **partial correctness only**.

All four Elgot laws hold.  The two easy ones (`naturality`, `uniformity`) are
proved by induction on the unrolling depth; `fixpoint` is an index shift; and
`codiagonal` is proved purely order-theoretically, from `bind_mono`,
`bot_bind`, `iUnion_bind`, `bind_iUnion` and `fixpoint` — it never mentions
traces, and so would work for any monad with a bottom and continuous unions.
-/

universe u

namespace Isotope.Elgot.RA

open Isotope.Elgot

variable {Loc Val : Type} {A B C : Type u}

namespace Comp

/-- The `i`-th unrolling: `f₀ := λ _. ⊥` and `f_{i+1} := f ; [id, f_i]`. -/
def approx (f : A → Comp Loc Val (B ⊕ A)) : ℕ → A → Comp Loc Val B
  | 0, _ => ⊥
  | n + 1, a => f a >>= Sum.elim pure (approx f n)

@[simp] theorem approx_zero (f : A → Comp Loc Val (B ⊕ A)) (a : A) :
    approx f 0 a = ⊥ := rfl

@[simp] theorem approx_succ (f : A → Comp Loc Val (B ⊕ A)) (n : ℕ) (a : A) :
    approx f (n + 1) a = f a >>= Sum.elim pure (approx f n) := rfl

/-- `f† := ⋃ᵢ fᵢ`. -/
def iterate (f : A → Comp Loc Val (B ⊕ A)) (a : A) : Comp Loc Val B :=
  iUnion (fun n : ℕ ↦ approx f n a)

instance : Iterate (Comp Loc Val) where
  iter := iterate

theorem iter_eq (f : A → Comp Loc Val (B ⊕ A)) : iter f = iterate f := rfl

theorem approx_le_iterate (f : A → Comp Loc Val (B ⊕ A)) (n : ℕ) (a : A) :
    approx f n a ≤ iterate f a := le_iUnion (fun n : ℕ ↦ approx f n a) n

theorem iterate_le {f : A → Comp Loc Val (B ⊕ A)} {a : A} {P : Comp Loc Val B}
    (h : ∀ n, approx f n a ≤ P) : iterate f a ≤ P := iUnion_le h

/-! ## Fixpoint -/

theorem fixpoint (f : A → Comp Loc Val (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  have h1 : (Sum.elim pure (iterate f) : B ⊕ A → Comp Loc Val B)
      = fun s ↦ iUnion (fun n : ℕ ↦ Sum.elim pure (approx f n) s) := by
    funext s
    cases s with
    | inl b => exact (iUnion_const (ι := ℕ) _).symm
    | inr a' => rfl
  change iterate f a = f a >>= Sum.elim pure (iterate f)
  rw [h1, bind_iUnion]
  apply le_antisymm
  · refine iterate_le (fun n ↦ ?_)
    cases n with
    | zero => exact bot_le
    | succ n => exact le_iUnion (fun n : ℕ ↦ f a >>= Sum.elim pure (approx f n)) n
  · exact iUnion_le (fun n ↦ approx_le_iterate f (n + 1) a)

theorem fixpoint_apply (f : A → Comp Loc Val (B ⊕ A)) (a : A) :
    iterate f a = f a >>= Sum.elim pure (iterate f) := congrFun (fixpoint f) a

/-! ## Naturality -/

theorem approx_bind (f : A → Comp Loc Val (B ⊕ A)) (g : B → Comp Loc Val C) :
    ∀ (n : ℕ) (a : A), approx f n a >>= g = approx (mapReturn f g) n a
  | 0, a => by simp [bot_bind]
  | n + 1, a => by
      change (f a >>= Sum.elim pure (approx f n)) >>= g
        = (f a >>= Sum.elim (fun b ↦ g b >>= pure ∘ Sum.inl) (pure ∘ Sum.inr))
          >>= Sum.elim pure (approx (mapReturn f g) n)
      rw [bind_assoc, bind_assoc]
      congr 1
      funext s
      cases s with
      | inl b =>
          simp only [Sum.elim_inl, bind_assoc, Function.comp_apply, pure_bind, bind_pure]
      | inr a' =>
          simp only [Sum.elim_inr, Function.comp_apply, pure_bind]
          exact approx_bind f g n a'

theorem naturality (f : A → Comp Loc Val (B ⊕ A)) (g : B → Comp Loc Val C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  change iterate f a >>= g = iterate (mapReturn f g) a
  rw [iterate, iUnion_bind]
  exact congrArg iUnion (funext fun n ↦ approx_bind f g n a)

/-! ## Pure uniformity -/

theorem approx_uniform (f : A → Comp Loc Val (B ⊕ A)) (g : C → Comp Loc Val (B ⊕ C))
    (h : A → C) (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    ∀ (n : ℕ) (a : A), approx f n a = approx g n (h a)
  | 0, _ => rfl
  | n + 1, a => by
      have hc : (f a >>= fun s ↦ (pure (Sum.map id h s) : Comp Loc Val (B ⊕ C))) = g (h a) := by
        have hcomm := congrFun comm a
        simp only [kcomp, liftPure, Function.comp_def, pure_bind] at hcomm
        exact hcomm
      change f a >>= Sum.elim pure (approx f n) = g (h a) >>= Sum.elim pure (approx g n)
      rw [← hc, bind_assoc]
      congr 1
      funext s
      cases s with
      | inl b => simp only [Sum.elim_inl, Sum.map_inl, id_eq, pure_bind]
      | inr a' =>
          simp only [Sum.elim_inr, Sum.map_inr, pure_bind]
          exact approx_uniform f g h comm n a'

theorem uniformity (f : A → Comp Loc Val (B ⊕ A)) (g : C → Comp Loc Val (B ⊕ C))
    (h : A → C) (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  funext a
  change iterate f a = pure (h a) >>= iterate g
  rw [pure_bind]
  exact congrArg iUnion (funext fun n ↦ approx_uniform f g h comm n a)

/-! ## Codiagonal

The argument is the thesis appendix's: `gᵢ ≤ (f†)†` by induction on `i`, and
`(f†)ᵢ ≤ g†` by two nested inductions, where `g = flattenBody f`. -/

/-- Unfolding `f†` once inside `f`. -/
theorem flatten_step (f : A → Comp Loc Val ((B ⊕ A) ⊕ A)) (a : A) :
    (f a >>= fun t ↦ Sum.elim pure (iterate (iterate f)) (flatten t))
      = iterate (iterate f) a := by
  rw [fixpoint_apply (iterate f) a, fixpoint_apply f a, bind_assoc]
  congr 1
  funext t
  cases t with
  | inl s => simp only [flatten, Sum.elim_inl, id_eq, pure_bind]
  | inr a' =>
      simp only [flatten, Sum.elim_inr]
      exact fixpoint_apply (iterate f) a'

theorem approx_flattenBody_le (f : A → Comp Loc Val ((B ⊕ A) ⊕ A)) :
    ∀ (n : ℕ) (a : A), approx (flattenBody f) n a ≤ iterate (iterate f) a
  | 0, _ => bot_le
  | n + 1, a => by
      change flattenBody f a >>= Sum.elim pure (approx (flattenBody f) n) ≤ _
      rw [flattenBody, kcomp, liftPure, bind_assoc]
      rw [← flatten_step f a]
      refine bind_mono_right (fun t ↦ ?_)
      rw [Function.comp_apply, pure_bind]
      cases t with
      | inl s =>
          cases s with
          | inl b => exact le_refl _
          | inr a' => exact approx_flattenBody_le f n a'
      | inr a' => exact approx_flattenBody_le f n a'

/-- The key induction for the other inclusion: any finite unrolling of `f`,
followed by `(flattenBody f)†` on the recursive summand, is below
`(flattenBody f)†`. -/
theorem approx_bind_iterate_flattenBody_le (f : A → Comp Loc Val ((B ⊕ A) ⊕ A)) :
    ∀ (n : ℕ) (a : A),
      (approx f n a >>= Sum.elim pure (iterate (flattenBody f))) ≤ iterate (flattenBody f) a
  | 0, _ => by rw [approx_zero, bot_bind]; exact bot_le
  | n + 1, a => by
      have hg := fixpoint_apply (flattenBody f) a
      rw [approx_succ, bind_assoc]
      calc (f a >>= fun t ↦ Sum.elim pure (approx f n) t
              >>= Sum.elim pure (iterate (flattenBody f)))
          ≤ f a >>= (fun t ↦ Sum.elim pure (iterate (flattenBody f)) (flatten t)) := by
            refine bind_mono_right (fun t ↦ ?_)
            cases t with
            | inl s => rw [Sum.elim_inl, pure_bind]; exact le_refl _
            | inr a' =>
                simp only [Sum.elim_inr, flatten, Sum.elim_inr]
                exact approx_bind_iterate_flattenBody_le f n a'
        _ = iterate (flattenBody f) a := by
            rw [hg, flattenBody, kcomp, liftPure, bind_assoc]
            congr 1
            funext t
            rw [Function.comp_apply, pure_bind]

/-- If one unfolding of `H` followed by `G` stays below `G`, then `G` bounds
every finite unrolling of `H`. -/
theorem approx_le_of_bind_le {H : A → Comp Loc Val (B ⊕ A)} {G : A → Comp Loc Val B}
    (h : ∀ a, H a >>= Sum.elim pure G ≤ G a) : ∀ (n : ℕ) (a : A), approx H n a ≤ G a
  | 0, _ => bot_le
  | n + 1, a => by
      refine le_trans (bind_mono_right (g := Sum.elim pure G) (fun s ↦ ?_)) (h a)
      cases s with
      | inl b => exact le_refl _
      | inr a' => exact approx_le_of_bind_le h n a'

theorem codiagonal (f : A → Comp Loc Val ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  change iterate (iterate f) a = iterate (flattenBody f) a
  refine le_antisymm (iterate_le (fun n ↦ ?_))
    (iterate_le (fun n ↦ approx_flattenBody_le f n a))
  exact approx_le_of_bind_le (H := iterate f) (G := iterate (flattenBody f))
    (fun a' ↦ by
      rw [iterate, iUnion_bind]
      exact iUnion_le (fun m ↦ approx_bind_iterate_flattenBody_le f m a')) n a

instance : LawfulElgotMonad (Comp Loc Val : Type u → Type u) where
  fixpoint f := fixpoint f
  naturality f g := naturality f g
  codiagonal f := codiagonal f
  uniformity f g h comm := uniformity f g h comm

end Comp

end Isotope.Elgot.RA
