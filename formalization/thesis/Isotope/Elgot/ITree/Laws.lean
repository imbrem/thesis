import Isotope.Elgot.ITree.Iteration

namespace Isotope.Elgot.ITree

open Isotope.Elgot

universe u

namespace Approx

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

/-- Act effectfully on the returned summand of a finite observation. -/
def mapReturn {E : Type u → Type u} {A B C : Type (u + 1)} (n : Nat)
    (x : Approx E (B ⊕ A) n) (g : B → Approx E C n) : Approx E (C ⊕ A) n :=
  bind n x (Sum.elim
    (fun b => bind n (g b) (fun c => (ret (E := E) (Sum.inl c)).observe n))
    (fun a => (ret (E := E) (Sum.inr a)).observe n))

/-- Residual-state simulation: effectful return mapping commutes with forgetting
the deepest visible observation. -/
theorem truncate_mapReturn {E : Type u → Type u} {A B C : Type (u + 1)}
    (n : Nat) (x : Approx E (B ⊕ A) (n + 1)) (g : B → Approx E C (n + 1)) :
    truncate n (mapReturn (n + 1) x g) =
      mapReturn n (truncate n x) (fun b => truncate n (g b)) := by
  rw [mapReturn, truncate_bind]
  unfold mapReturn
  apply congrArg (bind n (truncate n x))
  funext s
  cases s with
  | inl b =>
      simp only [Sum.elim_inl]
      rw [truncate_bind]
      apply congrArg (bind n (truncate n (g b)))
      funext c
      exact (ret (E := E) (Sum.inl c)).coherent n
  | inr a =>
      simp only [Sum.elim_inr]
      exact (ret (E := E) (Sum.inr a)).coherent n

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

end Isotope.Elgot.ITree
