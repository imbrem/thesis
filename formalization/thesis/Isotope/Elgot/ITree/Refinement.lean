import Isotope.Elgot.ITree.Handlers

/-!
# Divergence refinement

The equational theory of `Tree E` is not the whole story for the thesis: the
substructural-refinement development needs the *relational* one.  `Refines x y`
says `x` may diverge where `y` does not, but wherever `x` commits to a visible
head, `y` commits to the very same head and the continuations are again related.

It is defined as the greatest post-fixed point of `RefinesStep`, presented
concretely as "there exists a candidate relation containing the pair and closed
under one step".  `Refines.coind` is the coinduction principle, `Refines.dest`
the unfolding, and `Refines.step` the converse; together they say `Refines` is a
fixed point of `RefinesStep`.

Silent divergence is the least element (`diverge_refines`), refinement is a
partial order (`Tree.partialOrder`), and it is a congruence for `vis`, `bind`,
`map` and `translate`.  Antisymmetry is where finality earns its keep: it goes
through `Tree.eq_of_bisim'`.
-/

namespace Isotope.Elgot.ITree

universe u

variable {E F : Type u → Type u} {A B X : Type (u + 1)}


theorem Visible.vis_inj {S S' : Type u} {e : E S} {e' : E S'} {j : S → X} {j' : S' → X}
    (h : (Visible.vis e j : Visible E A X) = Visible.vis e' j') :
    ∃ _ : S = S', HEq e e' ∧ HEq j j' := by
  injection h with h1 h2 h3
  exact ⟨h1, h2, h3⟩

theorem Visible.vis_inj' {S : Type u} {e e' : E S} {j j' : S → X}
    (h : (Visible.vis e j : Visible E A X) = Visible.vis e' j') : e = e' ∧ j = j' := by
  obtain ⟨_, he, hj⟩ := Visible.vis_inj h
  exact ⟨eq_of_heq he, eq_of_heq hj⟩

/-- One step of divergence refinement, relative to a candidate relation. -/
def RefinesStep (R : Tree E A → Tree E A → Prop) (x y : Tree E A) : Prop :=
  x.destruct = Part.none ∨
  (∃ a : A, x.destruct = Part.some (.ret a) ∧ y.destruct = Part.some (.ret a)) ∨
  (∃ (S : Type u) (e : E S) (j j' : S → Tree E A),
    x.destruct = Part.some (.vis e j) ∧ y.destruct = Part.some (.vis e j') ∧
      ∀ s, R (j s) (j' s))

theorem RefinesStep.mono {R R' : Tree E A → Tree E A → Prop}
    (hRR : ∀ a b, R a b → R' a b) {x y : Tree E A} (h : RefinesStep R x y) :
    RefinesStep R' x y := by
  rcases h with h | h | ⟨S, e, j, j', hx, hy, hj⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨S, e, j, j', hx, hy, fun s => hRR _ _ (hj s)⟩)

/-- `x` refines to `y`: `x` may diverge where `y` does not, but wherever `x`
commits to a visible head, `y` commits to the same one. -/
def Refines (x y : Tree E A) : Prop :=
  ∃ R : Tree E A → Tree E A → Prop, (∀ a b, R a b → RefinesStep R a b) ∧ R x y

theorem Refines.coind (R : Tree E A → Tree E A → Prop)
    (hR : ∀ a b, R a b → RefinesStep R a b) {x y : Tree E A} (h : R x y) : Refines x y :=
  ⟨R, hR, h⟩

theorem Refines.dest {x y : Tree E A} (h : Refines x y) : RefinesStep Refines x y := by
  obtain ⟨R, hR, hxy⟩ := h
  exact RefinesStep.mono (fun a b hab => ⟨R, hR, hab⟩) (hR x y hxy)

theorem Refines.step {x y : Tree E A} (h : RefinesStep Refines x y) : Refines x y := by
  refine Refines.coind (fun a b => (a = x ∧ b = y) ∨ Refines a b) ?_ (Or.inl ⟨rfl, rfl⟩)
  rintro a b (⟨rfl, rfl⟩ | hab)
  · exact RefinesStep.mono (fun _ _ hc => Or.inr hc) h
  · exact RefinesStep.mono (fun _ _ hc => Or.inr hc) hab.dest

@[refl] theorem Refines.refl (t : Tree E A) : Refines t t := by
  refine Refines.coind Eq ?_ rfl
  rintro a b rfl
  rcases Tree.cases_three a with rfl | ⟨c, rfl⟩ | ⟨S, e, j, rfl⟩
  · exact Or.inl Tree.destruct_diverge
  · exact Or.inr (Or.inl ⟨c, Tree.destruct_ret c, Tree.destruct_ret c⟩)
  · exact Or.inr (Or.inr ⟨S, e, j, j, Tree.destruct_vis e j, Tree.destruct_vis e j,
      fun _ => rfl⟩)

/-- Silent divergence refines everything: it is the least element. -/
theorem diverge_refines (t : Tree E A) : Refines diverge t := by
  refine Refines.coind (fun a _ => a = diverge) ?_ rfl
  rintro a b rfl
  exact Or.inl Tree.destruct_diverge

theorem Refines.trans {x y z : Tree E A} (h₁ : Refines x y) (h₂ : Refines y z) :
    Refines x z := by
  refine Refines.coind (fun a c => ∃ b, Refines a b ∧ Refines b c) ?_ ⟨y, h₁, h₂⟩
  rintro a c ⟨b, hab, hbc⟩
  rcases hab.dest with hn | ⟨v, ha, hb⟩ | ⟨S, e, j, j', ha, hb, hj⟩
  · exact Or.inl hn
  · rcases hbc.dest with hn' | ⟨v', hb', hc⟩ | ⟨S', e', i, i', hb', _, _⟩
    · exact absurd (hb.symm.trans hn') (by simp)
    · rw [hb] at hb'
      cases Part.some_inj.mp hb'
      exact Or.inr (Or.inl ⟨v, ha, hc⟩)
    · rw [hb] at hb'
      exact absurd (Part.some_inj.mp hb') (by simp)
  · rcases hbc.dest with hn' | ⟨v', hb', _⟩ | ⟨S', e', i, i', hb', hc, hi⟩
    · exact absurd (hb.symm.trans hn') (by simp)
    · rw [hb] at hb'
      exact absurd (Part.some_inj.mp hb') (by simp)
    · rw [hb] at hb'
      obtain ⟨hS, he, hjj⟩ := Visible.vis_inj (Part.some_inj.mp hb')
      cases hS
      cases eq_of_heq he
      cases eq_of_heq hjj
      exact Or.inr (Or.inr ⟨S, e, j, i', ha, hc, fun s => ⟨j' s, hj s, hi s⟩⟩)

theorem Refines.antisymm {x y : Tree E A} (h₁ : Refines x y) (h₂ : Refines y x) : x = y := by
  refine Tree.eq_of_bisim' (fun a b => Refines a b ∧ Refines b a) ?_ ⟨h₁, h₂⟩
  rintro a b ⟨hab, hba⟩
  rcases hab.dest with hn | ⟨v, ha, hb⟩ | ⟨S, e, j, j', ha, hb, hj⟩
  · rcases hba.dest with hn' | ⟨v', hb', ha'⟩ | ⟨S', e', i, i', hb', ha', _⟩
    · exact Or.inl ⟨hn, hn'⟩
    · exact absurd (hn.symm.trans ha') (by simp)
    · exact absurd (hn.symm.trans ha') (by simp)
  · exact Or.inr (Or.inl ⟨v, ha, hb⟩)
  · rcases hba.dest with hn' | ⟨v', hb', _⟩ | ⟨S', e', i, i', hb', ha', hi⟩
    · exact absurd (hb.symm.trans hn') (by simp)
    · rw [hb] at hb'
      exact absurd (Part.some_inj.mp hb') (by simp)
    · rw [hb] at hb'
      obtain ⟨hS, he, hjj⟩ := Visible.vis_inj (Part.some_inj.mp hb')
      cases hS
      cases eq_of_heq he
      cases eq_of_heq hjj
      rw [ha] at ha'
      obtain ⟨he2, hjj2⟩ := Visible.vis_inj' (Part.some_inj.mp ha')
      cases hjj2
      exact Or.inr (Or.inr ⟨S, e, j, j', ha, hb, fun s => ⟨hj s, hi s⟩⟩)

/-- Only divergence refines divergence. -/
theorem refines_diverge_iff {t : Tree E A} : Refines t diverge ↔ t = diverge := by
  constructor
  · intro h
    rcases h.dest with hn | ⟨v, _, hd⟩ | ⟨S, e, j, j', _, hd, _⟩
    · exact (Tree.destruct_eq_none_iff t).mp hn
    · exact absurd (Tree.destruct_diverge.symm.trans hd) (by simp)
    · exact absurd (Tree.destruct_diverge.symm.trans hd) (by simp)
  · rintro rfl; exact Refines.refl _


/-! ## Congruence -/

/-- Refinement is a congruence for visible events. -/
theorem Refines.vis {S : Type u} (e : E S) {j j' : S → Tree E A}
    (hj : ∀ s, Refines (j s) (j' s)) : Refines (vis e j) (vis e j') :=
  Refines.step (Or.inr (Or.inr ⟨S, e, j, j', Tree.destruct_vis e j, Tree.destruct_vis e j', hj⟩))

/-- Refinement is a congruence for sequencing. -/
theorem Refines.bind {t s : Tree E A} {k l : A → Tree E B} (hts : Refines t s)
    (hkl : ∀ a, Refines (k a) (l a)) : Refines (t >>= k) (s >>= l) := by
  refine Refines.coind
    (fun x y => (∃ (t s : Tree E A) (k l : A → Tree E B), Refines t s ∧
        (∀ a, Refines (k a) (l a)) ∧ x = t >>= k ∧ y = s >>= l) ∨ Refines x y)
    ?_ (Or.inl ⟨t, s, k, l, hts, hkl, rfl, rfl⟩)
  rintro x y (⟨t, s, k, l, hts, hkl, rfl, rfl⟩ | hxy)
  · rcases hts.dest with hn | ⟨v, ha, hb⟩ | ⟨S, e, j, j', ha, hb, hj⟩
    · rw [(Tree.destruct_eq_none_iff t).mp hn, diverge_bind]
      exact Or.inl Tree.destruct_diverge
    · rw [Tree.eq_ret_of_destruct ha, Tree.eq_ret_of_destruct hb,
        show ((ret v : Tree E A) >>= k) = k v from pure_bind v k,
        show ((ret v : Tree E A) >>= l) = l v from pure_bind v l]
      exact RefinesStep.mono (fun _ _ hc => Or.inr hc) (hkl v).dest
    · rw [Tree.eq_vis_of_destruct ha, Tree.eq_vis_of_destruct hb, vis_bind, vis_bind]
      exact Or.inr (Or.inr ⟨S, e, _, _, Tree.destruct_vis _ _, Tree.destruct_vis _ _,
        fun s => Or.inl ⟨j s, j' s, k, l, hj s, hkl, rfl, rfl⟩⟩)
  · exact RefinesStep.mono (fun _ _ hc => Or.inr hc) hxy.dest

/-- Refinement is a congruence for `map`. -/
theorem Refines.map (f : A → B) {t s : Tree E A} (hts : Refines t s) :
    Refines (f <$> t) (f <$> s) := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  exact hts.bind (fun a => Refines.refl _)

/-- Refinement is a congruence for event relabelling. -/
theorem translate_refines (φ : ∀ R : Type u, E R → F R) {t s : Tree E A}
    (hts : Refines t s) : Refines (translate φ t) (translate φ s) := by
  refine Refines.coind
    (fun x y => ∃ t s : Tree E A, Refines t s ∧ x = translate φ t ∧ y = translate φ s)
    ?_ ⟨t, s, hts, rfl, rfl⟩
  rintro x y ⟨t, s, hts, rfl, rfl⟩
  rcases hts.dest with hn | ⟨v, ha, hb⟩ | ⟨S, e, j, j', ha, hb, hj⟩
  · rw [(Tree.destruct_eq_none_iff t).mp hn, translate_diverge]
    exact Or.inl Tree.destruct_diverge
  · rw [Tree.eq_ret_of_destruct ha, Tree.eq_ret_of_destruct hb, translate_ret]
    exact Or.inr (Or.inl ⟨v, Tree.destruct_ret v, Tree.destruct_ret v⟩)
  · rw [Tree.eq_vis_of_destruct ha, Tree.eq_vis_of_destruct hb, translate_vis, translate_vis]
    exact Or.inr (Or.inr ⟨S, φ S e, _, _, Tree.destruct_vis _ _, Tree.destruct_vis _ _,
      fun s => ⟨j s, j' s, hj s, rfl, rfl⟩⟩)

/-! ## The refinement order -/

/-- Divergence refinement is a partial order on trees, with `diverge` least. -/
@[reducible] def Tree.partialOrder (E : Type u → Type u) (A : Type (u + 1)) :
    PartialOrder (Tree E A) where
  le := Refines
  le_refl := Refines.refl
  le_trans := fun _ _ _ h₁ h₂ => h₁.trans h₂
  le_antisymm := fun _ _ h₁ h₂ => h₁.antisymm h₂

end Isotope.Elgot.ITree
