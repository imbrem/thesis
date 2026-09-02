import Isotope.Elgot.TraceSet.Iteration

/-!
# The Conway laws for finite-observation trace-set iteration

`fixpoint`, `naturality`, `codiagonal` and pure `uniformity` for
`TraceSet.iterate`, assuming only `Monoid E` and `MulAction E T`.
-/

namespace Isotope.Elgot

universe u

namespace TraceSet

variable {E T A B C : Type u} [Monoid E] [MulAction E T]

theorem fixpoint (f : A → TraceSet E T (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply ext
  intro u
  rw [mem_bind_iff]
  constructor
  · intro hr
    cases hr with
    | ret hs => exact Or.inl ⟨Sum.inl _, _, Trace.done _ 1, hs, rfl, by simp⟩
    | div hs => exact Or.inr ⟨_, hs, rfl⟩
    | more hs hr => exact Or.inl ⟨Sum.inr _, _, _, hs, hr, rfl⟩
  · rintro (⟨s, e, v, hs, hv, rfl⟩ | ⟨t, ht, rfl⟩)
    · cases s with
      | inl b =>
          have hv' : v = Trace.done b 1 := hv
          subst hv'
          simpa using Runs.ret hs
      | inr a' => exact Runs.more hs hv
    · exact Runs.div ht

theorem mem_mapReturn_iff (f : A → TraceSet E T (B ⊕ A)) (g : B → TraceSet E T C) (a : A)
    (w : Trace E T (C ⊕ A)) :
    w ∈ mapReturn f g a ↔
      (∃ b e v, Trace.done (Sum.inl b) e ∈ f a ∧ v ∈ g b ∧ w = e • Trace.map Sum.inl v) ∨
      (∃ a' e, Trace.done (Sum.inr a') e ∈ f a ∧ w = Trace.done (Sum.inr a') e) ∨
      (∃ t, Trace.inf t ∈ f a ∧ w = Trace.inf t) := by
  rw [show mapReturn f g a =
      f a >>= Sum.elim (fun b ↦ g b >>= pure ∘ Sum.inl) (pure ∘ Sum.inr) from rfl,
    mem_bind_iff]
  constructor
  · rintro (⟨s, e, v, hs, hv, rfl⟩ | ⟨t, ht, rfl⟩)
    · cases s with
      | inl b =>
          have hv2 : v ∈ (Sum.inl <$> g b : TraceSet E T (C ⊕ A)) := hv
          rcases (mem_map_iff Sum.inl (g b) v).1 hv2 with ⟨v', hv', rfl⟩
          exact Or.inl ⟨b, e, v', hs, hv', rfl⟩
      | inr a' =>
          have hv' : v = Trace.done (Sum.inr a') 1 := hv
          subst hv'
          exact Or.inr (Or.inl ⟨a', e, hs, by simp⟩)
    · exact Or.inr (Or.inr ⟨t, ht, rfl⟩)
  · rintro (⟨b, e, v, hs, hv, rfl⟩ | ⟨a', e, hs, rfl⟩ | ⟨t, ht, rfl⟩)
    · refine Or.inl ⟨Sum.inl b, e, Trace.map Sum.inl v, hs, ?_, rfl⟩
      exact (mem_map_iff Sum.inl (g b) _).2 ⟨v, hv, rfl⟩
    · exact Or.inl ⟨Sum.inr a', e, Trace.done (Sum.inr a') 1, hs, rfl, by simp⟩
    · exact Or.inr ⟨t, ht, rfl⟩

/-- Every finite run of `f` composed with a `g`-observation is a run of
`mapReturn f g`. -/
theorem runs_mapReturn_of_runs (f : A → TraceSet E T (B ⊕ A)) (g : B → TraceSet E T C)
    {a : A} {x : Trace E T B} (hr : Runs f a x) :
    ∀ v, v ∈ bindTrace x g → Runs (mapReturn f g) a v := by
  induction hr with
  | @ret a b e hs =>
      intro v hv
      rcases mem_smul.1 hv with ⟨w, hw, rfl⟩
      cases w with
      | done c e' =>
          refine Runs.ret ?_
          rw [mem_mapReturn_iff]
          exact Or.inl ⟨b, e, Trace.done c e', hs, hw, rfl⟩
      | inf t =>
          refine Runs.div ?_
          rw [mem_mapReturn_iff]
          exact Or.inl ⟨b, e, Trace.inf t, hs, hw, rfl⟩
  | @div a t hs =>
      intro v hv
      have hv' : v = Trace.inf t := hv
      subst hv'
      refine Runs.div ?_
      rw [mem_mapReturn_iff]
      exact Or.inr (Or.inr ⟨t, hs, rfl⟩)
  | @more a a' e x' hs _ ih =>
      intro v hv
      rw [smul_bindTrace] at hv
      rcases mem_smul.1 hv with ⟨w, hw, rfl⟩
      refine Runs.more ?_ (ih w hw)
      rw [mem_mapReturn_iff]
      exact Or.inr (Or.inl ⟨a', e, hs, rfl⟩)

theorem runs_mapReturn_iff (f : A → TraceSet E T (B ⊕ A)) (g : B → TraceSet E T C) (a : A)
    (w : Trace E T C) :
    Runs (mapReturn f g) a w ↔ ∃ x, Runs f a x ∧ w ∈ bindTrace x g := by
  constructor
  · intro hr
    induction hr with
    | @ret a c e hs =>
        rw [mem_mapReturn_iff] at hs
        rcases hs with (⟨b, e₁, v, hb, hv, heq⟩ | ⟨a', e₁, _, heq⟩ | ⟨t, _, heq⟩)
        · rcases Trace.smul_eq_done_iff.mp heq.symm with ⟨e₂, hmap, rfl⟩
          rcases (Trace.map_eq_done_iff Sum.inl).mp hmap with ⟨c', rfl, hc⟩
          cases hc
          exact ⟨Trace.done b e₁, Runs.ret hb, mem_smul.2 ⟨_, hv, rfl⟩⟩
        · exact absurd heq (by simp)
        · exact absurd heq (by simp)
    | @div a t hs =>
        rw [mem_mapReturn_iff] at hs
        rcases hs with (⟨b, e₁, v, hb, hv, heq⟩ | ⟨a', e₁, _, heq⟩ | ⟨t', ht', heq⟩)
        · rcases Trace.smul_eq_inf_iff.mp heq.symm with ⟨t₂, hmap, rfl⟩
          rw [Trace.map_eq_inf_iff] at hmap
          subst hmap
          exact ⟨Trace.done b e₁, Runs.ret hb, mem_smul.2 ⟨Trace.inf t₂, hv, rfl⟩⟩
        · exact absurd heq (by simp)
        · cases heq
          exact ⟨_, Runs.div ht', rfl⟩
    | @more a a' e w' hs _ ih =>
        rw [mem_mapReturn_iff] at hs
        rcases hs with (⟨b, e₁, v, _, _, heq⟩ | ⟨a'', e₁, hstep, heq⟩ | ⟨t, _, heq⟩)
        · rcases Trace.smul_eq_done_iff.mp heq.symm with ⟨e₂, hmap, _⟩
          rcases (Trace.map_eq_done_iff Sum.inl).mp hmap with ⟨c', _, hc⟩
          exact absurd hc (by simp)
        · cases heq
          rcases ih with ⟨x, hx, hw⟩
          refine ⟨_, Runs.more hstep hx, ?_⟩
          rw [smul_bindTrace]
          exact mem_smul.2 ⟨w', hw, rfl⟩
        · exact absurd heq (by simp)
  · rintro ⟨x, hx, hw⟩
    exact runs_mapReturn_of_runs f g hx w hw

theorem naturality (f : A → TraceSet E T (B ⊕ A)) (g : B → TraceSet E T C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  apply ext
  intro w
  constructor
  · intro h
    rcases (mem_kcomp_iff' (iter f) g a w).1 h with ⟨v, hv, hw⟩
    exact (runs_mapReturn_iff f g a w).2 ⟨v, hv, hw⟩
  · intro h
    rcases (runs_mapReturn_iff f g a w).1 h with ⟨v, hv, hw⟩
    exact (mem_kcomp_iff' (iter f) g a w).2 ⟨v, hv, hw⟩

theorem mem_flattenBody_iff (f : A → TraceSet E T ((B ⊕ A) ⊕ A)) (a : A)
    (w : Trace E T (B ⊕ A)) :
    w ∈ flattenBody f a ↔ ∃ v, v ∈ f a ∧ w = Trace.map flatten v := by
  rw [show flattenBody f a = (flatten <$> f a : TraceSet E T (B ⊕ A)) from rfl, mem_map_iff]

/-- One induction covering all three ways an `f`-run can be spliced into a run of
`flattenBody f`. -/
theorem runs_flatten_step (f : A → TraceSet E T ((B ⊕ A) ⊕ A)) {a : A}
    {x : Trace E T (B ⊕ A)} (hr : Runs f a x) :
    ∀ v, v ∈ bindTrace x (Sum.elim pure (iter (flattenBody f))) → Runs (flattenBody f) a v := by
  induction hr with
  | @ret a s e hs =>
      intro v hv
      rcases mem_smul.1 hv with ⟨w, hw, rfl⟩
      cases s with
      | inl b =>
          have hw' : w = Trace.done b 1 := hw
          subst hw'
          simp only [Trace.smul_done, mul_one]
          refine Runs.ret ?_
          rw [mem_flattenBody_iff]
          exact ⟨_, hs, rfl⟩
      | inr a' =>
          refine Runs.more ?_ hw
          rw [mem_flattenBody_iff]
          exact ⟨_, hs, rfl⟩
  | @div a t hs =>
      intro v hv
      have hv' : v = Trace.inf t := hv
      subst hv'
      refine Runs.div ?_
      rw [mem_flattenBody_iff]
      exact ⟨_, hs, rfl⟩
  | @more a a' e x' hs _ ih =>
      intro v hv
      rw [smul_bindTrace] at hv
      rcases mem_smul.1 hv with ⟨w, hw, rfl⟩
      refine Runs.more ?_ (ih w hw)
      rw [mem_flattenBody_iff]
      exact ⟨_, hs, rfl⟩

theorem runs_flatten_of_nested (f : A → TraceSet E T ((B ⊕ A) ⊕ A)) {a : A}
    {w : Trace E T B} (hr : Runs (iter f) a w) : Runs (flattenBody f) a w := by
  induction hr with
  | @ret a b e hs =>
      refine runs_flatten_step f (x := Trace.done (Sum.inl b) e) hs _ ?_
      exact mem_smul.2 ⟨Trace.done b 1, rfl, by simp⟩
  | @div a t hs => exact runs_flatten_step f (x := Trace.inf t) hs _ rfl
  | @more a a' e w' hs _ ih =>
      refine runs_flatten_step f (x := Trace.done (Sum.inr a') e) hs _ ?_
      exact mem_smul.2 ⟨w', ih, rfl⟩

theorem runs_nested_of_flatten (f : A → TraceSet E T ((B ⊕ A) ⊕ A)) {a : A}
    {w : Trace E T B} (hr : Runs (flattenBody f) a w) : Runs (iter f) a w := by
  induction hr with
  | @ret a b e hs =>
      rw [mem_flattenBody_iff] at hs
      rcases hs with ⟨v, hv, heq⟩
      rcases (Trace.map_eq_done_iff flatten).mp heq.symm with ⟨s, rfl, hb⟩
      cases s with
      | inl s' =>
          cases s' with
          | inl b' =>
              cases hb
              exact Runs.ret (Runs.ret hv)
          | inr a' => cases hb
      | inr a' => cases hb
  | @div a t hs =>
      rw [mem_flattenBody_iff] at hs
      rcases hs with ⟨v, hv, heq⟩
      have heq' := (Trace.map_eq_inf_iff flatten).mp heq.symm
      subst heq'
      exact Runs.div (Runs.div hv)
  | @more a a' e w' hs _ ih =>
      rw [mem_flattenBody_iff] at hs
      rcases hs with ⟨v, hv, heq⟩
      rcases (Trace.map_eq_done_iff flatten).mp heq.symm with ⟨s, rfl, hb⟩
      cases s with
      | inl s' =>
          cases s' with
          | inl b => cases hb
          | inr a'' =>
              cases hb
              exact Runs.more (Runs.ret hv) ih
      | inr a'' =>
          cases hb
          cases ih with
          | ret hi => exact Runs.ret (Runs.more hv hi)
          | div hi => exact Runs.div (Runs.more hv hi)
          | @more _ a₃ e₁ w₂ hi ht =>
              have hstep : Runs (iter f) a ((e * e₁) • w₂) :=
                Runs.more (Runs.more hv hi) ht
              rwa [Trace.smul_smul_trace] at hstep

theorem codiagonal (f : A → TraceSet E T ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply ext
  intro w
  exact ⟨runs_flatten_of_nested f, runs_nested_of_flatten f⟩

/-- The commuting square, read as a one-step membership bijection. -/
theorem uniform_step (f : A → TraceSet E T (B ⊕ A)) (g : C → TraceSet E T (B ⊕ C))
    (h : A → C) (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    (a : A) (w : Trace E T (B ⊕ C)) :
    w ∈ g (h a) ↔ ∃ v, v ∈ f a ∧ w = Trace.map (Sum.map id h) v := by
  have square := congrFun comm a
  have h1 : kcomp f (liftPure (Sum.map id h)) a
      = ((Sum.map id h) <$> f a : TraceSet E T (B ⊕ C)) := rfl
  have h2 : kcomp (liftPure h) g a = g (h a) := by
    change (pure (h a) : TraceSet E T C) >>= g = g (h a)
    exact pure_bind (h a) g
  rw [h1, h2] at square
  rw [← square, mem_map_iff]

theorem runs_uniform_forward (f : A → TraceSet E T (B ⊕ A)) (g : C → TraceSet E T (B ⊕ C))
    (h : A → C) (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    {a : A} {w : Trace E T B} (hr : Runs f a w) : Runs g (h a) w := by
  induction hr with
  | @ret a b e hs =>
      refine Runs.ret ?_
      rw [uniform_step f g h comm]
      exact ⟨Trace.done (Sum.inl b) e, hs, rfl⟩
  | @div a t hs =>
      refine Runs.div ?_
      rw [uniform_step f g h comm]
      exact ⟨Trace.inf t, hs, rfl⟩
  | @more a a' e w' hs _ ih =>
      refine Runs.more ?_ ih
      rw [uniform_step f g h comm]
      exact ⟨Trace.done (Sum.inr a') e, hs, rfl⟩

theorem runs_uniform_reverse (f : A → TraceSet E T (B ⊕ A)) (g : C → TraceSet E T (B ⊕ C))
    (h : A → C) (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g)
    {c : C} {w : Trace E T B} (hr : Runs g c w) : ∀ a, c = h a → Runs f a w := by
  induction hr with
  | @ret c b e hs =>
      intro a ha
      subst ha
      rw [uniform_step f g h comm] at hs
      rcases hs with ⟨v, hv, heq⟩
      rcases (Trace.map_eq_done_iff (Sum.map id h)).mp heq.symm with ⟨s, rfl, hb⟩
      cases s with
      | inl b' =>
          cases hb
          exact Runs.ret hv
      | inr a' => cases hb
  | @div c t hs =>
      intro a ha
      subst ha
      rw [uniform_step f g h comm] at hs
      rcases hs with ⟨v, hv, heq⟩
      have heq' := (Trace.map_eq_inf_iff (Sum.map id h)).mp heq.symm
      subst heq'
      exact Runs.div hv
  | @more c c' e w' hs _ ih =>
      intro a ha
      subst ha
      rw [uniform_step f g h comm] at hs
      rcases hs with ⟨v, hv, heq⟩
      rcases (Trace.map_eq_done_iff (Sum.map id h)).mp heq.symm with ⟨s, rfl, hb⟩
      cases s with
      | inl b => cases hb
      | inr a' =>
          cases hb
          exact Runs.more hv (ih a' rfl)

theorem uniformity (f : A → TraceSet E T (B ⊕ A)) (g : C → TraceSet E T (B ⊕ C))
    (h : A → C) (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  funext a
  apply ext
  intro w
  have h2 : kcomp (liftPure h) (iter g) a = iter g (h a) := by
    change (pure (h a) : TraceSet E T C) >>= (iter g) = iter g (h a)
    exact pure_bind (h a) (iter g)
  rw [h2]
  exact ⟨fun hr ↦ runs_uniform_forward f g h comm hr,
    fun hr ↦ runs_uniform_reverse f g h comm hr a rfl⟩

instance instLawfulElgotMonad : LawfulElgotMonad (TraceSet E T) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end TraceSet

end Isotope.Elgot
