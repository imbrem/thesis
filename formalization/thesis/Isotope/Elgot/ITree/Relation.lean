import Isotope.Elgot.ITree.Refinement

/-!
# Heterogeneous relation lifting

`Tree.Rel RA` lifts a relation `RA` on values to one on trees: the two trees
must both diverge, both return `RA`-related values, or both emit the same event
with related continuations, coinductively.  This is the tau-insensitive `eutt`
of this carrier, and it generalises both `Bisim` (`bisim_iff_rel_eq`) and the
one-sided `Refines`.

Like `Refines` it is the greatest post-fixed point of a one-step condition,
presented as an existentially quantified candidate relation, with `coind`,
`dest` and `step`.  The key identification is `Tree.rel_eq_iff`: relating trees
by value equality is exactly equality of trees, which is `Tree.eq_of_bisim'` in
disguise.
-/

namespace Isotope.Elgot.ITree

universe u

variable {E : Type u → Type u} {A B C : Type (u + 1)}


/-- One step of a heterogeneous tree relation, relative to a candidate. -/
def RelStep (RA : A → B → Prop) (R : Tree E A → Tree E B → Prop)
    (x : Tree E A) (y : Tree E B) : Prop :=
  (x.destruct = Part.none ∧ y.destruct = Part.none) ∨
  (∃ (a : A) (b : B), RA a b ∧
    x.destruct = Part.some (.ret a) ∧ y.destruct = Part.some (.ret b)) ∨
  (∃ (S : Type u) (e : E S) (j : S → Tree E A) (j' : S → Tree E B),
    x.destruct = Part.some (.vis e j) ∧ y.destruct = Part.some (.vis e j') ∧
      ∀ s, R (j s) (j' s))

theorem RelStep.mono {RA : A → B → Prop} {R R' : Tree E A → Tree E B → Prop}
    (hRR : ∀ a b, R a b → R' a b) {x : Tree E A} {y : Tree E B}
    (h : RelStep RA R x y) : RelStep RA R' x y := by
  rcases h with h | h | ⟨S, e, j, j', hx, hy, hj⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨S, e, j, j', hx, hy, fun s => hRR _ _ (hj s)⟩)

/-- Lift a relation on values to one on trees: matching heads all the way down. -/
def Tree.Rel (RA : A → B → Prop) (x : Tree E A) (y : Tree E B) : Prop :=
  ∃ R : Tree E A → Tree E B → Prop, (∀ a b, R a b → RelStep RA R a b) ∧ R x y

theorem Tree.Rel.coind (RA : A → B → Prop) (R : Tree E A → Tree E B → Prop)
    (hR : ∀ a b, R a b → RelStep RA R a b) {x : Tree E A} {y : Tree E B} (h : R x y) :
    Tree.Rel RA x y := ⟨R, hR, h⟩

theorem Tree.Rel.dest {RA : A → B → Prop} {x : Tree E A} {y : Tree E B}
    (h : Tree.Rel RA x y) : RelStep RA (Tree.Rel RA) x y := by
  obtain ⟨R, hR, hxy⟩ := h
  exact RelStep.mono (fun a b hab => ⟨R, hR, hab⟩) (hR x y hxy)

theorem Tree.Rel.step {RA : A → B → Prop} {x : Tree E A} {y : Tree E B}
    (h : RelStep RA (Tree.Rel RA) x y) : Tree.Rel RA x y := by
  refine Tree.Rel.coind RA (fun a b => (a = x ∧ b = y) ∨ Tree.Rel RA a b) ?_ (Or.inl ⟨rfl, rfl⟩)
  rintro a b (⟨rfl, rfl⟩ | hab)
  · exact RelStep.mono (fun _ _ hc => Or.inr hc) h
  · exact RelStep.mono (fun _ _ hc => Or.inr hc) hab.dest

theorem Tree.Rel.mono {RA RA' : A → B → Prop} (hRA : ∀ a b, RA a b → RA' a b)
    {x : Tree E A} {y : Tree E B} (h : Tree.Rel RA x y) : Tree.Rel RA' x y := by
  refine Tree.Rel.coind RA' (Tree.Rel RA) ?_ h
  intro a b hab
  rcases hab.dest with h1 | ⟨v, w, hvw, hx, hy⟩ | ⟨S, e, j, j', hx, hy, hj⟩
  · exact Or.inl h1
  · exact Or.inr (Or.inl ⟨v, w, hRA v w hvw, hx, hy⟩)
  · exact Or.inr (Or.inr ⟨S, e, j, j', hx, hy, hj⟩)

@[refl] theorem Tree.Rel.refl {RA : A → A → Prop} (hRA : ∀ a, RA a a) (t : Tree E A) :
    Tree.Rel RA t t := by
  refine Tree.Rel.coind RA Eq ?_ rfl
  rintro a b rfl
  rcases Tree.cases_three a with rfl | ⟨c, rfl⟩ | ⟨S, e, j, rfl⟩
  · exact Or.inl ⟨Tree.destruct_diverge, Tree.destruct_diverge⟩
  · exact Or.inr (Or.inl ⟨c, c, hRA c, Tree.destruct_ret c, Tree.destruct_ret c⟩)
  · exact Or.inr (Or.inr ⟨S, e, j, j, Tree.destruct_vis e j, Tree.destruct_vis e j,
      fun _ => rfl⟩)

/-- Relating trees by equality of values is equality of trees. -/
theorem Tree.rel_eq_iff {x y : Tree E A} : Tree.Rel Eq x y ↔ x = y := by
  constructor
  · intro h
    refine Tree.eq_of_bisim' (Tree.Rel (E := E) (A := A) Eq) ?_ h
    intro a b hab
    rcases hab.dest with h1 | ⟨v, w, rfl, hx, hy⟩ | ⟨S, e, j, j', hx, hy, hj⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨v, hx, hy⟩)
    · exact Or.inr (Or.inr ⟨S, e, j, j', hx, hy, hj⟩)
  · rintro rfl; exact Tree.Rel.refl (fun _ => rfl) x

/-- Weak bisimulation is relation lifting along equality. -/
theorem bisim_iff_rel_eq {x y : Tree E A} : Bisim x y ↔ Tree.Rel Eq x y := by
  rw [bisim_iff_eq, Tree.rel_eq_iff]

/-- Relation lifting is a congruence for visible events. -/
theorem Tree.Rel.vis {RA : A → B → Prop} {S : Type u} (e : E S) {j : S → Tree E A}
    {j' : S → Tree E B} (hj : ∀ s, Tree.Rel RA (j s) (j' s)) :
    Tree.Rel RA (vis e j) (vis e j') :=
  Tree.Rel.step (Or.inr (Or.inr ⟨S, e, j, j', Tree.destruct_vis e j, Tree.destruct_vis e j', hj⟩))

/-- Relation lifting is a congruence for returns. -/
theorem Tree.Rel.ret {RA : A → B → Prop} {a : A} {b : B} (h : RA a b) :
    Tree.Rel (E := E) RA (ret a) (ret b) :=
  Tree.Rel.step (Or.inr (Or.inl ⟨a, b, h, Tree.destruct_ret a, Tree.destruct_ret b⟩))

/-- Relation lifting is a congruence for divergence. -/
theorem Tree.Rel.diverge {RA : A → B → Prop} :
    Tree.Rel (E := E) RA diverge diverge :=
  Tree.Rel.step (Or.inl ⟨Tree.destruct_diverge, Tree.destruct_diverge⟩)

/-- Relation lifting is a congruence for sequencing. -/
theorem Tree.Rel.bind {RA : A → B → Prop} {RC : C → C → Prop}
    {t : Tree E A} {s : Tree E B} {k : A → Tree E C} {l : B → Tree E C}
    (hts : Tree.Rel RA t s) (hkl : ∀ a b, RA a b → Tree.Rel RC (k a) (l b)) :
    Tree.Rel RC (t >>= k) (s >>= l) := by
  refine Tree.Rel.coind RC
    (fun x y => (∃ (t : Tree E A) (s : Tree E B), Tree.Rel RA t s ∧ x = t >>= k ∧ y = s >>= l)
      ∨ Tree.Rel RC x y)
    ?_ (Or.inl ⟨t, s, hts, rfl, rfl⟩)
  rintro x y (⟨t, s, hts, rfl, rfl⟩ | hxy)
  · rcases hts.dest with ⟨hx, hy⟩ | ⟨v, w, hvw, hx, hy⟩ | ⟨S, e, j, j', hx, hy, hj⟩
    · rw [(Tree.destruct_eq_none_iff t).mp hx, (Tree.destruct_eq_none_iff s).mp hy,
        diverge_bind, diverge_bind]
      exact Or.inl ⟨Tree.destruct_diverge, Tree.destruct_diverge⟩
    · rw [Tree.eq_ret_of_destruct hx, Tree.eq_ret_of_destruct hy,
        show ((ITree.ret v : Tree E A) >>= k) = k v from pure_bind v k,
        show ((ITree.ret w : Tree E B) >>= l) = l w from pure_bind w l]
      exact RelStep.mono (fun _ _ hc => Or.inr hc) (hkl v w hvw).dest
    · rw [Tree.eq_vis_of_destruct hx, Tree.eq_vis_of_destruct hy, vis_bind, vis_bind]
      exact Or.inr (Or.inr ⟨S, e, _, _, Tree.destruct_vis _ _, Tree.destruct_vis _ _,
        fun s => Or.inl ⟨j s, j' s, hj s, rfl, rfl⟩⟩)
  · exact RelStep.mono (fun _ _ hc => Or.inr hc) hxy.dest

end Isotope.Elgot.ITree
