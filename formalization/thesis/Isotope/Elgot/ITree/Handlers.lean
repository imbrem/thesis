import Isotope.Elgot.ITree.Structural

/-!
# Event relabelling and interpretation

Two corecursive constructions over the final coalgebra structure.

* `translate φ` relabels every visible event along a signature morphism
  `φ : ∀ R, E R → F R`, leaving the tree shape untouched.  It is computable, and
  is a monad morphism (`translate_bind`) functorial in the signature
  (`translate_id`, `translate_translate`).
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

variable {F G : Type u → Type u} {B : Type (u + 1)}

/-- The coalgebra unfolded by `translate`: relabel the head event, keep the
children. -/
def translateStep (φ : ∀ R : Type u, E R → F R) (s : Tree E A) :
    Part (Visible F A (Tree E A)) :=
  (fun v => match v with
    | Visible.ret a => Visible.ret a
    | Visible.vis e k => Visible.vis (φ _ e) k) <$> s.destruct

/-- Relabel every visible event along a signature morphism. -/
def translate (φ : ∀ R : Type u, E R → F R) (t : Tree E A) : Tree F A :=
  corec (translateStep φ) t

/-- Destructing a relabelled tree. -/
@[simp] theorem Tree.destruct_translate (φ : ∀ R : Type u, E R → F R) (t : Tree E A) :
    (translate φ t).destruct = (fun v => match v with
      | Visible.ret a => Visible.ret a
      | Visible.vis e k => Visible.vis (φ _ e) (fun r => translate φ (k r)))
        <$> t.destruct := by
  rw [translate, Tree.destruct_corec, translateStep]
  simp only [Part.map_eq_map, Part.map_map]
  refine congrArg (fun g => Part.map g t.destruct) (funext fun v => ?_)
  cases v <;> rfl

/-- Relabelling a return. -/
@[simp] theorem translate_ret (φ : ∀ R : Type u, E R → F R) (a : A) :
    translate φ (ret a) = ret a := by
  rw [← Tree.construct_destruct (translate φ (ret a)), Tree.destruct_translate]
  simp

/-- Relabelling silent divergence. -/
@[simp] theorem translate_diverge (φ : ∀ R : Type u, E R → F R) :
    translate φ (diverge : Tree E A) = diverge := by
  rw [← Tree.construct_destruct (translate φ diverge), Tree.destruct_translate]
  simp

/-- Relabelling a visible event. -/
@[simp] theorem translate_vis (φ : ∀ R : Type u, E R → F R) {R : Type u}
    (e : E R) (k : R → Tree E A) :
    translate φ (vis e k) = vis (φ R e) (fun r => translate φ (k r)) := by
  rw [← Tree.construct_destruct (translate φ (vis e k)), Tree.destruct_translate]
  simp

/-- Relabelling along the identity does nothing. -/
@[simp] theorem translate_id (t : Tree E A) : translate (fun _ e => e) t = t := by
  refine Tree.eq_of_bisim' (fun x y => x = translate (fun _ e => e) y) ?_ rfl
  rintro x y rfl
  rcases Tree.cases_three y with rfl | ⟨a, rfl⟩ | ⟨S, e, j, rfl⟩
  · simp
  · simp
  · exact Or.inr (Or.inr ⟨S, e, fun r => translate (fun _ e => e) (j r), j,
      by simp, by simp, fun s => rfl⟩)

/-- Relabelling twice is relabelling once along the composite. -/
theorem translate_translate (φ : ∀ R : Type u, E R → F R) (ψ : ∀ R : Type u, F R → G R)
    (t : Tree E A) :
    translate ψ (translate φ t) = translate (fun R e => ψ R (φ R e)) t := by
  refine Tree.eq_of_bisim'
    (fun x y => ∃ s : Tree E A, x = translate ψ (translate φ s)
      ∧ y = translate (fun R e => ψ R (φ R e)) s) ?_ ⟨t, rfl, rfl⟩
  rintro x y ⟨s, rfl, rfl⟩
  rcases Tree.cases_three s with rfl | ⟨a, rfl⟩ | ⟨S, e, j, rfl⟩
  · simp
  · simp
  · exact Or.inr (Or.inr ⟨S, ψ S (φ S e),
      fun r => translate ψ (translate φ (j r)),
      fun r => translate (fun R e => ψ R (φ R e)) (j r),
      by simp, by simp, fun r => ⟨j r, rfl, rfl⟩⟩)

/-- Relabelling commutes with sequencing: `translate φ` is a monad morphism. -/
theorem translate_bind (φ : ∀ R : Type u, E R → F R) (t : Tree E A) (k : A → Tree E B) :
    translate φ (t >>= k) = translate φ t >>= fun a => translate φ (k a) := by
  refine Tree.eq_of_bisim'
    (fun x y => x = y ∨ ∃ (s : Tree E A) (j : A → Tree E B),
      x = translate φ (s >>= j) ∧ y = translate φ s >>= fun a => translate φ (j a))
    ?_ (Or.inr ⟨t, k, rfl, rfl⟩)
  rintro x y (rfl | ⟨s, j, rfl, rfl⟩)
  · exact Tree.bisim'_refl
      (fun x y => x = y ∨ ∃ (s : Tree E A) (j : A → Tree E B),
      x = translate φ (s >>= j) ∧ y = translate φ s >>= fun a => translate φ (j a))
      (fun _ => Or.inl rfl) x
  · rcases Tree.cases_three s with rfl | ⟨a, rfl⟩ | ⟨S, e, i, rfl⟩
    · rw [diverge_bind, translate_diverge, translate_diverge, diverge_bind]
      exact Or.inl ⟨Tree.destruct_diverge, Tree.destruct_diverge⟩
    · rw [show ((ret a : Tree E A) >>= j) = j a from pure_bind a j, translate_ret,
        show ((ret a : Tree F A) >>= fun a => translate φ (j a)) = translate φ (j a) from
          pure_bind a _]
      exact Tree.bisim'_refl
        (fun x y => x = y ∨ ∃ (s : Tree E A) (j : A → Tree E B),
        x = translate φ (s >>= j) ∧ y = translate φ s >>= fun a => translate φ (j a))
        (fun _ => Or.inl rfl) _
    · rw [vis_bind, translate_vis, translate_vis, vis_bind]
      exact Or.inr (Or.inr ⟨S, φ S e,
        fun r => translate φ (i r >>= j),
        fun r => translate φ (i r) >>= fun a => translate φ (j a),
        by simp, by simp, fun r => Or.inr ⟨i r, j, rfl, rfl⟩⟩)

end Translate

/-! ## Interpretation into an Elgot monad -/

section Interp

open Isotope.Elgot

variable {F : Type u → Type u} {B : Type (u + 1)}
  {M : Type (u + 1) → Type (u + 1)} [Monad M] [Iterate M]

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

omit [Iterate M] [LawfulMonad M] [LawfulElgotMonad M] in
/-- One interpretation step on a visible event: run the handler, then continue
with the residual tree. -/
@[simp] theorem interpStep_vis (h : ∀ R : Type u, E R → M (ULift.{u + 1} R)) {R : Type u}
    (e : E R) (k : R → Tree E A) :
    interpStep h (vis e k) = h R e >>= fun r => pure (Sum.inr (k r.down)) := by
  simp only [interpStep, Tree.destruct_vis]
  rw [dif_pos (show (Part.some (Visible.vis e k : Visible E A (Tree E A))).Dom from trivial)]
  rfl

/-- Interpreting a single triggered event is the handler itself. -/
@[simp] theorem interp_trigger {R : Type u} (h : ∀ R : Type u, E R → M (ULift.{u + 1} R))
    (e : E R) : interp h (trigger e) = h R e := by
  rw [trigger, interp_vis]
  refine Eq.trans (congrArg (h R e >>= ·) (funext fun r => ?_)) (bind_pure (h R e))
  rw [show (ULift.up r.down : ULift.{u + 1} R) = r from rfl]
  exact interp_ret h r

/-- The divergent element of an iterative monad: iterate a body that never
returns. -/
def divergent (M : Type (u + 1) → Type (u + 1)) [Monad M] [Iterate M] (B : Type (u + 1)) :
    M B :=
  Isotope.Elgot.iter (fun _ : PUnit.{u + 2} => (pure (Sum.inr PUnit.unit) : M (B ⊕ PUnit))) ⟨⟩

/-- Interpreting silent divergence gives the target's divergent element. -/
theorem interp_diverge (h : ∀ R : Type u, E R → M (ULift.{u + 1} R)) :
    interp h (diverge : Tree E A) = divergent M A := by
  have hu := LawfulElgotMonad.uniformity
    (fun _ : PUnit.{u + 2} => (pure (Sum.inr PUnit.unit) : M (A ⊕ PUnit)))
    (interpStep h (E := E) (A := A)) (fun _ => diverge) ?_
  · rw [divergent, hu, kcomp, liftPure, Function.comp_apply, pure_bind, interp]
  · funext x
    simp only [kcomp, liftPure, Function.comp_apply, pure_bind, interpStep_diverge]
    rfl

/-- Interpretation commutes with `map`. -/
theorem interp_map (h : ∀ R : Type u, E R → M (ULift.{u + 1} R)) (f : A → B) (t : Tree E A) :
    interp h (f <$> t) = f <$> interp h t := by
  have hu := LawfulElgotMonad.uniformity
    (mapReturn (interpStep h (E := E) (A := A)) (liftPure f))
    (interpStep h (E := E) (A := B)) (fun s => f <$> s) ?_
  · have hnat := LawfulElgotMonad.naturality (interpStep h (E := E) (A := A)) (liftPure f)
    have hc : (kcomp (Isotope.Elgot.iter (interpStep h (E := E) (A := A))) (liftPure f)) t
        = (kcomp (liftPure (fun s : Tree E A => f <$> s))
            (Isotope.Elgot.iter (interpStep h (E := E) (A := B)))) t := by
      rw [hnat, hu]
    simp only [interp, ← bind_pure_comp]
    simpa [kcomp, liftPure, Function.comp_def] using hc.symm
  · funext s
    simp only [kcomp, liftPure, Function.comp_apply, mapReturn, Function.comp_def,
      bind_assoc, pure_bind]
    rcases Tree.cases_three s with rfl | ⟨a, rfl⟩ | ⟨R, e, j, rfl⟩
    · simp
    · simp
    · simp

/-- Interpretation absorbs relabelling. -/
theorem interp_translate (φ : ∀ R : Type u, E R → F R)
    (h : ∀ R : Type u, F R → M (ULift.{u + 1} R)) (t : Tree E A) :
    interp h (translate φ t) = interp (fun R e => h R (φ R e)) t := by
  have hu := LawfulElgotMonad.uniformity
    (interpStep (fun R e => h R (φ R e)) (E := E) (A := A))
    (interpStep h (E := F) (A := A)) (fun s => translate φ s) ?_
  · have hc := congrFun hu t
    simpa [kcomp, liftPure, Function.comp_apply, interp] using hc.symm
  · funext s
    simp only [kcomp, liftPure, Function.comp_apply, pure_bind]
    rcases Tree.cases_three s with rfl | ⟨a, rfl⟩ | ⟨R, e, j, rfl⟩
    · simp
    · simp
    · simp

end Interp

end Isotope.Elgot.ITree
