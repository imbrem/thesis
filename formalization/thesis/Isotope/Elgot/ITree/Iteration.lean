import Isotope.Elgot.ITree.Monad

/-!
# Iteration on weak interaction trees

Iteration is again defined depth by depth.  At a fixed depth the loop is a
`Part`-iteration: `Approx.iterStep` either commits to a visible layer or feeds a
new state back, so productivity is inherited from the complete Elgot structure
of `Part`.  The coherence square `Approx.truncate_iter` is the substantial
lemma; it is proved from naturality and uniformity for `Part`.
-/

namespace Isotope.Elgot.ITree

open Isotope.Elgot

universe u

namespace Approx

/-- Iterate a finite observation.  Recursive returns are discharged by `Part.iter`;
visible continuations recurse at strictly smaller observation depth. -/
noncomputable def iter {E : Type u → Type u} {A B : Type (u + 1)} :
    (n : Nat) → Approx E (B ⊕ A) n → (A → Approx E (B ⊕ A) n) → Approx E B n
  | 0, _, _ => PUnit.unit
  | n + 1, x, f => Isotope.Elgot.iter (fun x => x >>= fun
      | .ret (.inl b) => Part.some (.inl (.ret b))
      | .ret (.inr a) => Part.some (.inr (f a))
      | .vis e next => Part.some (.inl (.vis e (fun r =>
          iter n (next r) (fun a => truncate n (f a)))))) x

/-- One partial step of iteration at a fixed observation depth. -/
noncomputable def iterStep {E : Type u → Type u} {A B : Type (u + 1)} (n : Nat)
    (f : A → Approx E (B ⊕ A) (n + 1)) :
    Approx E (B ⊕ A) (n + 1) →
      Part (Visible E B (Approx E B n) ⊕ Approx E (B ⊕ A) (n + 1)) :=
  fun x => x >>= fun
    | .ret (.inl b) => Part.some (.inl (.ret b))
    | .ret (.inr a) => Part.some (.inr (f a))
    | .vis e next => Part.some (.inl (.vis e (fun r =>
        iter n (next r) (fun a => truncate n (f a)))))

/-- Unfold one visible layer of `Approx.iter`. -/
@[simp] theorem iter_succ {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1)) (f : A → Approx E (B ⊕ A) (n + 1)) :
    iter (n + 1) x f = Isotope.Elgot.iter (iterStep n f) x := rfl

/-- The commuting square feeding the uniformity step of `truncate_iter`. -/
private theorem truncate_iterStep_square {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (f : A → Approx E (B ⊕ A) (n + 2))
    (ih : ∀ (x : Approx E (B ⊕ A) (n + 1)),
      truncate n (iter (n + 1) x (fun a => truncate (n + 1) (f a))) =
        iter n (truncate n x) (fun a => truncate n (truncate (n + 1) (f a)))) :
    kcomp (mapReturn (iterStep (n + 1) f)
        (liftPure (Visible.map (truncate n))))
        (liftPure (Sum.map id (truncate (E := E) (A := B ⊕ A) (n + 1)))) =
      kcomp (liftPure (truncate (E := E) (A := B ⊕ A) (n + 1)))
        (iterStep n (fun a => truncate (n + 1) (f a))) := by
  funext x
  simp [kcomp, mapReturn, liftPure, Function.comp_apply, iterStep,
    truncate, Part.map_eq_map, Part.bind_assoc, Part.bind_map]
  apply congrArg (Part.bind x)
  funext node
  cases node with
  | ret s =>
      cases s <;> simp
  | vis e next =>
      simp
      congr
      funext r
      exact ih (next r)

/-- Truncation commutes with iteration of finite observations. -/
theorem truncate_iter {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1))
    (f : A → Approx E (B ⊕ A) (n + 1)) :
    truncate n (iter (n + 1) x f) =
      iter n (truncate n x) (fun a => truncate n (f a)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change (Visible.map (truncate n) <$> Isotope.Elgot.iter (iterStep (n + 1) f) x) = _
      have hn := LawfulElgotMonad.naturality (m := Part)
        (iterStep (n + 1) f) (liftPure (Visible.map (truncate n)))
      have hu := LawfulElgotMonad.uniformity (m := Part)
        (mapReturn (iterStep (n + 1) f) (liftPure (Visible.map (truncate n))))
        (iterStep n (fun a => truncate (n + 1) (f a)))
        (truncate (E := E) (A := B ⊕ A) (n + 1))
        (truncate_iterStep_square n f (fun y => ih y (fun a => truncate (n + 1) (f a))))
      calc
        Visible.map (truncate n) <$> Isotope.Elgot.iter (iterStep (n + 1) f) x =
            kcomp (Isotope.Elgot.iter (iterStep (n + 1) f))
              (liftPure (Visible.map (truncate n))) x := by
                symm
                exact Part.bind_some_eq_map _ _
        _ = Isotope.Elgot.iter
            (mapReturn (iterStep (n + 1) f) (liftPure (Visible.map (truncate n)))) x :=
              congrFun hn x
        _ = kcomp (liftPure (truncate (E := E) (A := B ⊕ A) (n + 1)))
            (Isotope.Elgot.iter (iterStep n (fun a => truncate (n + 1) (f a)))) x :=
              congrFun hu x
        _ = iter (n + 1) (truncate (n + 1) x) (fun a => truncate (n + 1) (f a)) := by
              simp [kcomp, liftPure]

end Approx

/-- Complete iteration for weak interaction trees. -/
noncomputable def iterate {E : Type u → Type u} {A B : Type (u + 1)}
    (f : A → Tree E (B ⊕ A)) (a : A) : Tree E B where
  observe n := Approx.iter n ((f a).observe n) (fun a => (f a).observe n)
  coherent n := by
    rw [Approx.truncate_iter]
    congr 1
    · exact (f a).coherent n
    · funext a
      exact (f a).coherent n

/-- Weak interaction trees carry an iteration operator. -/
noncomputable instance instIterate (E : Type u → Type u) : Iterate (Tree E) where
  iter := iterate

/-- The observations of an iteration. -/
@[simp] theorem observe_iter {E : Type u → Type u} {A B : Type (u + 1)}
    (f : A → Tree E (B ⊕ A)) (a : A) (n : Nat) :
    (Isotope.Elgot.iter f a).observe n =
      Approx.iter n ((f a).observe n) (fun a => (f a).observe n) := rfl

end Isotope.Elgot.ITree
