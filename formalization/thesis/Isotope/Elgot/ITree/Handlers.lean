import Isotope.Elgot.ITree.Structural

/-!
# Event relabelling and interpretation

Two corecursive constructions over the final coalgebra structure.

* `translate φ` relabels every visible event along a signature morphism
  `φ : ∀ R, E R → F R`, leaving the tree shape untouched.  It is computable.
* `interp h` interprets an interaction tree into *any* monad with iteration by
  iterating a single head-exposing step, so a diverging tree is sent to the
  target's divergent element.  Deciding whether a tree has a visible head is a
  `Part.Dom` test, so `interp` is classical.

The computation lemmas all follow the same recipe, which generalises to every
corecursive definition over `destruct`: rewrite backwards through
`Tree.construct_destruct`, unfold the definition, apply `Tree.destruct_corec`,
and simplify the resulting `Part.map`.
-/

namespace Isotope.Elgot.ITree

universe u

variable {E : Type u → Type u} {A : Type (u + 1)}

/-! ## Relabelling events -/

section Translate

variable {F : Type u → Type u}

/-- Relabel every visible event along a signature morphism. -/
def translate (φ : ∀ R : Type u, E R → F R) (t : Tree E A) : Tree F A :=
  corec (fun s : Tree E A => (fun v => match v with
    | Visible.ret a => Visible.ret a
    | Visible.vis e k => Visible.vis (φ _ e) k) <$> s.destruct) t

/-- Relabelling a return. -/
@[simp] theorem translate_ret (φ : ∀ R : Type u, E R → F R) (a : A) :
    translate φ (ret a) = ret a := by
  rw [← Tree.construct_destruct (translate φ (ret a)), translate, Tree.destruct_corec]
  simp only [Tree.destruct_ret, Part.map_eq_map, Part.map_some]
  rfl

/-- Relabelling silent divergence. -/
@[simp] theorem translate_diverge (φ : ∀ R : Type u, E R → F R) :
    translate φ (diverge : Tree E A) = diverge := by
  rw [← Tree.construct_destruct (translate φ diverge), translate, Tree.destruct_corec]
  simp

/-- Relabelling a visible event. -/
@[simp] theorem translate_vis (φ : ∀ R : Type u, E R → F R) {R : Type u}
    (e : E R) (k : R → Tree E A) :
    translate φ (vis e k) = vis (φ R e) (fun r => translate φ (k r)) := by
  rw [← Tree.construct_destruct (translate φ (vis e k)), translate, Tree.destruct_corec]
  simp only [Tree.destruct_vis, Part.map_eq_map, Part.map_some]
  rfl

end Translate

/-! ## Interpretation into an Elgot monad -/

section Interp

open Isotope.Elgot

variable {M : Type (u + 1) → Type (u + 1)} [Monad M] [Iterate M]

/-- One step of interpretation: expose the head of a tree in the target monad,
returning `inl` on a value and `inr` on a residual tree.  A tree with no visible
head is its own residual, so iterating diverges. -/
noncomputable def interpStep (h : ∀ R : Type u, E R → M (ULift.{u + 1} R))
    (s : Tree E A) : M (A ⊕ Tree E A) :=
  open Classical in
  if hd : s.destruct.Dom then
    match s.destruct.get hd with
    | .ret a => pure (Sum.inl a)
    | .vis e k => h _ e >>= fun r => pure (Sum.inr (k r.down))
  else pure (Sum.inr s)

/-- Interpret an interaction tree into any monad with iteration. -/
noncomputable def interp (h : ∀ R : Type u, E R → M (ULift.{u + 1} R))
    (t : Tree E A) : M A := Isotope.Elgot.iter (interpStep h) t

variable [LawfulMonad M] [LawfulElgotMonad M]

omit [Iterate M] [LawfulMonad M] [LawfulElgotMonad M] in
/-- One interpretation step on a return. -/
@[simp] theorem interpStep_ret (h : ∀ R : Type u, E R → M (ULift.{u + 1} R)) (a : A) :
    interpStep h (ret a) = (pure (Sum.inl a) : M (A ⊕ Tree E A)) := by
  simp only [interpStep, Tree.destruct_ret]
  rw [dif_pos (show (Part.some (Visible.ret a : Visible E A (Tree E A))).Dom from trivial)]
  rfl

omit [Iterate M] [LawfulMonad M] [LawfulElgotMonad M] in
/-- One interpretation step on silent divergence: no progress. -/
@[simp] theorem interpStep_diverge (h : ∀ R : Type u, E R → M (ULift.{u + 1} R)) :
    interpStep h (diverge : Tree E A) = pure (Sum.inr diverge) := by
  simp only [interpStep, Tree.destruct_diverge]
  rw [dif_neg (show ¬ (Part.none : Part (Visible E A (Tree E A))).Dom from id)]

/-- Interpreting a return. -/
theorem interp_ret (h : ∀ R : Type u, E R → M (ULift.{u + 1} R)) (a : A) :
    interp h (ret a) = (pure a : M A) := by
  rw [interp, LawfulElgotMonad.fixpoint (interpStep h)]
  simp

/-- Interpreting a visible event: run the handler, then continue. -/
theorem interp_vis {R : Type u} (h : ∀ R : Type u, E R → M (ULift.{u + 1} R))
    (e : E R) (k : R → Tree E A) :
    interp h (vis e k) = h _ e >>= fun r => interp h (k r.down) := by
  rw [interp, LawfulElgotMonad.fixpoint (interpStep h)]
  simp only [interpStep, Tree.destruct_vis]
  rw [dif_pos (show (Part.some (Visible.vis e k : Visible E A (Tree E A))).Dom from trivial)]
  change (h R e >>= fun r => pure (Sum.inr (k r.down))) >>= _ = _
  rw [bind_assoc]
  refine congrArg _ (funext fun r => ?_)
  rw [pure_bind]
  rfl

end Interp

end Isotope.Elgot.ITree
