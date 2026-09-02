import Isotope.Elgot.ITree.Bisim

/-!
# Worked examples of weak interaction trees

Return, visible events, silent steps, a finite loop, and silent divergence, all
as proved equations in the weak model.
-/

namespace Isotope.Elgot.ITree

open Isotope.Elgot

universe u

/-- The fixpoint law, applied at a point. -/
theorem iterate_apply {E : Type u → Type u} {A B : Type (u + 1)}
    (f : A → Tree E (B ⊕ A)) (a : A) :
    Isotope.Elgot.iter f a = f a >>= Sum.elim pure (Isotope.Elgot.iter f) :=
  congrFun (iterate_fixpoint f) a

/-- A silent step is invisible: `tau` is the identity, so it is absorbed by
sequencing on both sides. -/
theorem tau_bind {E : Type u → Type u} {A B : Type (u + 1)}
    (t : Tree E A) (k : A → Tree E B) : tau t >>= k = t >>= k := rfl

/-- Silent divergence absorbs sequencing. -/
theorem diverge_bind {E : Type u → Type u} {A B : Type (u + 1)}
    (k : A → Tree E B) : (diverge : Tree E A) >>= k = diverge := by
  apply Tree.ext
  intro n
  cases n with
  | zero => exact Approx.eq_zero _ _
  | succ n =>
      change Approx.bind (n + 1) ((diverge : Tree E A).observe (n + 1))
          (fun a => (k a).observe (n + 1)) = _
      rw [observe_diverge, observe_diverge]
      simp [Approx.bind]

/-- Sequencing pushes under a visible event. -/
theorem vis_bind {E : Type u → Type u} {A B : Type (u + 1)} {R : Type u}
    (e : E R) (k : R → Tree E A) (h : A → Tree E B) :
    vis e k >>= h = vis e (fun r => k r >>= h) := by
  apply Tree.ext
  intro n
  cases n with
  | zero => exact Approx.eq_zero _ _
  | succ n =>
      change Approx.bind (n + 1) ((vis e k).observe (n + 1))
          (fun a => (h a).observe (n + 1)) = (vis e (fun r => k r >>= h)).observe (n + 1)
      rw [observe_vis, observe_vis]
      simp only [Approx.bind, Part.bind_eq_bind, Part.bind_some]
      congr 1
      refine congrArg (Visible.vis e) (funext fun r => ?_)
      change Approx.bind n ((k r).observe n)
          (fun a => Approx.truncate n ((h a).observe (n + 1))) = _
      apply congrArg (Approx.bind n ((k r).observe n))
      funext a
      exact (h a).coherent n

/-- A single visible event returning its (universe-lifted) response. -/
def trigger {E : Type u → Type u} {R : Type u} (e : E R) : Tree E (ULift.{u + 1} R) :=
  vis e (fun r => ret (ULift.up r))

/-- A loop that returns immediately returns. -/
theorem iterate_ret_inl {E : Type u → Type u} {A B : Type (u + 1)} (b : B) (a : A) :
    Isotope.Elgot.iter (fun _ : A => (ret (Sum.inl b) : Tree E (B ⊕ A))) a = ret b := by
  rw [iterate_apply]
  change (pure (Sum.inl b) : Tree E (B ⊕ A)) >>= _ = _
  rw [pure_bind]
  rfl

/-- A `Part`-iteration whose body returns to the state it started from never
completes a finite run, hence diverges. -/
theorem part_iter_self {X Y : Type (u + 1)} (g : X → Part (Y ⊕ X)) (x : X)
    (hx : g x = Part.some (Sum.inr x)) :
    Isotope.Elgot.iter g x = Part.none := by
  apply Part.ext
  intro y
  simp only [Part.notMem_none, iff_false]
  intro hmem
  rw [Isotope.Elgot.Part.mem_iter_iff] at hmem
  have key : ∀ (z : X) (w : Y), Isotope.Elgot.Part.Runs g z w → z = x → False := by
    intro z w hr
    induction hr with
    | done hs =>
        intro hz
        subst hz
        rw [hx] at hs
        cases Part.mem_some_iff.mp hs
    | more hs _ ih =>
        intro hz
        subst hz
        rw [hx] at hs
        exact ih (Sum.inr.inj (Part.mem_some_iff.mp hs))
  exact key x y hmem rfl

/-- An unproductive loop is silent divergence.  This is the law that fails for
strongly bisimilar interaction trees and holds here. -/
theorem iterate_ret_inr {E : Type u → Type u} {A B : Type (u + 1)} (a : A) :
    Isotope.Elgot.iter (fun a : A => (ret (Sum.inr a) : Tree E (B ⊕ A))) a =
      (diverge : Tree E B) := by
  apply Tree.ext
  intro n
  cases n with
  | zero => exact Approx.eq_zero _ _
  | succ n =>
      rw [observe_iter, observe_diverge, Approx.iter_succ]
      apply part_iter_self
      simp [Approx.iterStep, observe_ret]

/-- A loop body that returns after exactly two iterations. -/
def twoStepBody {E : Type u → Type u} {B : Type (u + 1)} (b : B) :
    ULift.{u + 1} Bool → Tree E (B ⊕ ULift.{u + 1} Bool)
  | ⟨true⟩ => ret (Sum.inr ⟨false⟩)
  | ⟨false⟩ => ret (Sum.inl b)

/-- A finite loop runs to completion. -/
theorem iterate_twoStepBody {E : Type u → Type u} {B : Type (u + 1)} (b : B) :
    Isotope.Elgot.iter (twoStepBody (E := E) b) ⟨true⟩ = ret b := by
  rw [iterate_apply]
  change (pure (Sum.inr (⟨false⟩ : ULift.{u + 1} Bool)) :
      Tree E (B ⊕ ULift.{u + 1} Bool)) >>= _ = _
  rw [pure_bind]
  change Isotope.Elgot.iter (twoStepBody (E := E) b) ⟨false⟩ = _
  rw [iterate_apply]
  change (pure (Sum.inl b) : Tree E (B ⊕ ULift.{u + 1} Bool)) >>= _ = _
  rw [pure_bind]
  rfl

/-- A loop guarded by a visible event is productive: it unfolds to an infinite
tree of events rather than collapsing to divergence. -/
theorem iterate_vis_loop {E : Type u → Type u} {A B : Type (u + 1)} {R : Type u}
    (e : E R) (a : A) :
    Isotope.Elgot.iter
        (fun a : A => (vis e (fun _ => ret (Sum.inr a)) : Tree E (B ⊕ A))) a =
      vis e (fun _ => Isotope.Elgot.iter
        (fun a : A => (vis e (fun _ => ret (Sum.inr a)) : Tree E (B ⊕ A))) a) := by
  conv_lhs => rw [iterate_apply]
  change vis e (fun _ => (ret (Sum.inr a) : Tree E (B ⊕ A))) >>= _ = _
  rw [vis_bind]
  refine congrArg (vis e) (funext fun _ => ?_)
  change (pure (Sum.inr a) : Tree E (B ⊕ A)) >>= _ = _
  rw [pure_bind]
  rfl

/-- A productive loop is not divergence. -/
theorem iterate_vis_loop_ne_diverge {E : Type u → Type u} {A B : Type (u + 1)}
    {R : Type u} (e : E R) (a : A) :
    Isotope.Elgot.iter
        (fun a : A => (vis e (fun _ => ret (Sum.inr a)) : Tree E (B ⊕ A))) a ≠
      (diverge : Tree E B) := by
  rw [iterate_vis_loop]
  exact vis_ne_diverge e _

end Isotope.Elgot.ITree
