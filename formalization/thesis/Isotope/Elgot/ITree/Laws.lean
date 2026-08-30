import Isotope.Elgot.ITree.Iteration

namespace Isotope.Elgot.ITree

open Isotope.Elgot

universe u

namespace Approx

/-- Act effectfully on the returned summand of a finite observation. -/
def mapReturn {E : Type u → Type u} {A B C : Type (u + 1)} (n : Nat)
    (x : Approx E (B ⊕ A) n) (g : B → Approx E C n) : Approx E (C ⊕ A) n :=
  bind n x (Sum.elim
    (fun b => bind n (g b) (fun c => (ret (E := E) (Sum.inl c)).observe n))
    (fun a => (ret (E := E) (Sum.inr a)).observe n))

/-- Postprocess one returned visible observation. -/
def post {E : Type u → Type u} {B C : Type (u + 1)} (n : Nat)
    (g : B → Approx E C (n + 1)) :
    Visible E B (Approx E B n) → Part (Visible E C (Approx E C n))
  | .ret b => g b
  | .vis e next => Part.some (.vis e (fun r => bind n (next r)
      (fun b => truncate n (g b))))

@[simp] theorem mapReturn_succ {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1)) (g : B → Approx E C (n + 1)) :
    mapReturn (n + 1) x g = x >>= fun
      | .ret (.inl b) => post n g (.ret b)
      | .ret (.inr a) => Part.some (.ret (.inr a))
      | .vis e next => Part.some (.vis e (fun r => mapReturn n (next r)
          (fun b => truncate n (g b)))) := by
  rfl

theorem iter_fixpoint {E : Type u → Type u} {A B : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) n) (f : A → Approx E (B ⊕ A) n) :
    iter n x f = bind n x (Sum.elim
      (fun b => (ret (E := E) b).observe n)
      (fun a => iter n (f a) f)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iter_succ, LawfulElgotMonad.fixpoint]
      simp only [iterStep, bind, LawfulMonad.bind_assoc]
      apply congrArg (x >>= ·)
      funext node
      cases node with
      | ret s =>
          cases s <;> simp [ret]
      | vis e next =>
          simp
          congr
          funext r
          rw [ih (next r) (fun a => truncate n (f a))]
          apply congrArg (bind n (next r))
          funext s
          cases s with
          | inl b => exact ((ret (E := E) b).coherent n).symm
          | inr a => exact (truncate_iter n (f a) f).symm

private theorem naturality_square {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (f : A → Approx E (B ⊕ A) (n + 1))
    (g : B → Approx E C (n + 1))
    (ih : ∀ x, bind n (iter n x (fun a => truncate n (f a)))
        (fun b => truncate n (g b)) =
      iter n (mapReturn n x (fun b => truncate n (g b)))
        (fun a => mapReturn n (truncate n (f a)) (fun b => truncate n (g b)))) :
    kcomp (mapReturn (iterStep n f) (post n g))
        (liftPure (Sum.map id (fun x => mapReturn (n + 1) x g))) =
      kcomp (liftPure (fun x => mapReturn (n + 1) x g))
        (iterStep n (fun a => mapReturn (n + 1) (f a) g)) := by
  funext x
  simp [kcomp, Isotope.Elgot.mapReturn, liftPure, iterStep, post, mapReturn,
    Part.bind_assoc, Part.bind_map, truncate, Part.map_eq_map]
  apply congrArg (Part.bind x)
  funext node
  cases node with
  | ret s =>
      cases s with
      | inl b =>
          apply congrArg (Part.bind (g b))
          funext node
          cases node with
          | ret c => rfl
          | vis e next =>
              simp
              congr
              funext r
              exact ih (next r)
      | inr a => rfl
  | vis e next =>
      simp
      congr
      funext r
      exact ih (next r)

theorem iter_naturality {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) n) (f : A → Approx E (B ⊕ A) n)
    (g : B → Approx E C n) :
    bind n (iter n x f) g = iter n (mapReturn n x g) (fun a => mapReturn n (f a) g) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change kcomp (Isotope.Elgot.iter (iterStep n f)) (post n g) x = _
      rw [LawfulElgotMonad.naturality]
      rw [LawfulElgotMonad.uniformity
        (mapReturn (iterStep n f) (post n g))
        (iterStep n (fun a => mapReturn (n + 1) (f a) g))
        (fun x => mapReturn (n + 1) x g)
        (naturality_square n f g (fun y => ih y (fun a => truncate n (f a))
          (fun b => truncate n (g b))))]
      rfl

end Approx

/-- The defining fixpoint equation for weak interaction-tree iteration. -/
theorem iterate_fixpoint {E : Type u → Type u} {A B : Type (u + 1)}
    (f : A → Tree E (B ⊕ A)) :
    Isotope.Elgot.iter f = fun a => f a >>= Sum.elim pure (Isotope.Elgot.iter f) := by
  funext a
  apply Tree.ext
  intro n
  rw [observe_iter, observe_bind]
  rw [Approx.iter_fixpoint]
  apply congrArg (Approx.bind n ((f a).observe n))
  funext s
  cases s with
  | inl b => rfl
  | inr a => exact observe_iter f a n

theorem iterate_naturality {E : Type u → Type u} {A B C : Type (u + 1)}
    (f : A → Tree E (B ⊕ A)) (g : B → Tree E C) :
    kcomp (Isotope.Elgot.iter f) g =
      Isotope.Elgot.iter (Isotope.Elgot.mapReturn f g) := by
  funext a
  apply Tree.ext
  intro n
  rw [observe_bind, observe_iter]
  change Approx.bind n (Approx.iter n ((f a).observe n) (fun a => (f a).observe n))
      (fun b => (g b).observe n) = _
  rw [Approx.iter_naturality]
  rfl

end Isotope.Elgot.ITree
