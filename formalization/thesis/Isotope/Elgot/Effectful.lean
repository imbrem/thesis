import Isotope.Elgot.Basic

/-!
# The effect-observing partiality monad

`Eff A` refines `Part A` by recording, alongside the partial result, whether the
computation performed an effect.  Crucially, the effect flag is meaningful even
for computations that never return: a loop that diverges after running an
impure instruction is distinguished from a loop that diverges silently.

This is exactly the distinction that defeats *completeness* of the λ-iter
equational theory with respect to observational equivalence in state models: the
two loops

```
iter a { ι_r x : ι_r x }        and        iter a { ι_r x : let _ = f x; ι_r x }
```

are observationally indistinguishable in every state model, but they receive
different denotations here, and `Eff` is a `LawfulElgotMonad`, so the equational
theory cannot prove them equal.

We use the same convention as `Isotope.Elgot.Basic`: `Sum.inl` is a returned
value and `Sum.inr` is a recursive call.
-/

namespace Isotope.Elgot

universe u

/-- A partial computation together with the proposition "an effect was
performed".  The flag is *not* required to be supported by the partial value:
`⟨Part.none, True⟩` is the denotation of a diverging computation that
nevertheless ran an effect. -/
@[ext]
structure Eff (A : Type u) where
  /-- The partial result of the computation. -/
  val : _root_.Part A
  /-- Whether the computation performed an effect. -/
  ran : Prop

namespace Eff

variable {A B C : Type u}

/-- The underlying `Part`-valued Kleisli arrow of an `Eff`-valued one. -/
def valFun (f : A → Eff B) : A → _root_.Part B := fun a ↦ (f a).val

/-- `valFun` is pointwise projection. -/
@[simp] theorem valFun_apply (f : A → Eff B) (a : A) : valFun f a = (f a).val := rfl

/-- `pure` performs no effect; a bind performs one if either stage does, where the
continuation is only reached at values the first stage actually returns. -/
instance instMonad : Monad Eff where
  pure a := ⟨_root_.Part.some a, False⟩
  bind x k := ⟨x.val >>= fun a ↦ (k a).val, x.ran ∨ ∃ a, a ∈ x.val ∧ (k a).ran⟩

/-- `pure` returns immediately. -/
@[simp] theorem val_pure (a : A) : (pure a : Eff A).val = _root_.Part.some a := rfl

/-- `pure` performs no effect. -/
@[simp] theorem ran_pure (a : A) : (pure a : Eff A).ran = False := rfl

/-- The partial value of a bind is the bind of the partial values. -/
@[simp] theorem val_bind (x : Eff A) (k : A → Eff B) :
    (x >>= k).val = x.val >>= fun a ↦ (k a).val := rfl

/-- A bind performs an effect if its first stage does, or if some value it returns
leads to a continuation that does. -/
@[simp] theorem ran_bind (x : Eff A) (k : A → Eff B) :
    (x >>= k).ran = (x.ran ∨ ∃ a, a ∈ x.val ∧ (k a).ran) := rfl

/-- Membership in the partial value of a bind. -/
theorem mem_bind_val_iff {x : Eff A} {k : A → Eff B} {b : B} :
    b ∈ (x >>= k).val ↔ ∃ a, a ∈ x.val ∧ b ∈ (k a).val := by
  change b ∈ x.val.bind (fun a ↦ (k a).val) ↔ _
  exact _root_.Part.mem_bind_iff

/-- `Eff` is a lawful monad: the value components are the `Part` laws, and the
effect components are propositional equivalences. -/
instance instLawfulMonad : LawfulMonad Eff := LawfulMonad.mk'
  (m := Eff)
  (id_map := fun x ↦ by
    apply Eff.ext
    · change x.val >>= pure = x.val
      exact bind_pure x.val
    · apply propext
      constructor
      · rintro (h | ⟨_, _, h⟩)
        · exact h
        · exact h.elim
      · exact Or.inl)
  (pure_bind := fun x f ↦ by
    apply Eff.ext
    · change _root_.Part.some x >>= (fun a ↦ (f a).val) = (f x).val
      exact pure_bind x _
    · apply propext
      constructor
      · rintro (h | ⟨a, ha, h⟩)
        · exact h.elim
        · have : a = x := _root_.Part.mem_some_iff.mp ha
          exact this ▸ h
      · exact fun h ↦ Or.inr ⟨x, _root_.Part.mem_some x, h⟩)
  (bind_assoc := fun x f g ↦ by
    apply Eff.ext
    · change x.val >>= valFun f >>= valFun g = x.val >>= fun a ↦ (f a).val >>= valFun g
      exact bind_assoc x.val (valFun f) (valFun g)
    · apply propext
      constructor
      · rintro ((h | ⟨a, ha, h⟩) | ⟨b, hb, h⟩)
        · exact Or.inl h
        · exact Or.inr ⟨a, ha, Or.inl h⟩
        · obtain ⟨a, ha, hb⟩ := mem_bind_val_iff.mp hb
          exact Or.inr ⟨a, ha, Or.inr ⟨b, hb, h⟩⟩
      · rintro (h | ⟨a, ha, h | ⟨b, hb, h⟩⟩)
        · exact Or.inl (Or.inl h)
        · exact Or.inl (Or.inr ⟨a, ha, h⟩)
        · exact Or.inr ⟨b, mem_bind_val_iff.mpr ⟨a, ha, hb⟩, h⟩)

/-! ## Reachable loop states -/

/-- `Reaches f a a'` holds when the loop state `a'` is visited by the iteration
body `f` started from the loop state `a`. -/
inductive Reaches {A B : Type u} (f : A → Eff (B ⊕ A)) : A → A → Prop
  /-- Every loop state reaches itself. -/
  | refl (a : A) : Reaches f a a
  /-- A recursive call extends reachability. -/
  | step {a a' a'' : A} : Sum.inr a' ∈ (f a).val → Reaches f a' a'' → Reaches f a a''

/-- Reachability is transitive. -/
theorem Reaches.trans {f : A → Eff (B ⊕ A)} {a a' a'' : A}
    (h : Reaches f a a') (h' : Reaches f a' a'') : Reaches f a a'' := by
  induction h with
  | refl _ => exact h'
  | step hs _ ih => exact .step hs (ih h')

/-- Reachability only depends on the recursive calls the body can make. -/
theorem Reaches.mono {f : A → Eff (B ⊕ A)} {g : A → Eff (C ⊕ A)}
    (hfg : ∀ a a' : A, Sum.inr a' ∈ (f a).val → Sum.inr a' ∈ (g a).val)
    {a a' : A} (h : Reaches f a a') : Reaches g a a' := by
  induction h with
  | refl a => exact .refl a
  | step hs _ ih => exact .step (hfg _ _ hs) ih

/-! ## Iteration -/

/-- Iteration returns the ordinary partial value of the `Part`-level iteration, and
records an effect exactly when some reachable loop state performs one -- including
when the loop never returns. -/
noncomputable instance instIterate : Iterate Eff where
  iter f a := ⟨Elgot.iter (valFun f) a, ∃ a', Reaches f a a' ∧ (f a').ran⟩

/-- The partial value of an iteration is the `Part`-level iteration. -/
@[simp] theorem val_iter (f : A → Eff (B ⊕ A)) (a : A) :
    (iter f a).val = Elgot.iter (valFun f) a := rfl

/-- An iteration performs an effect iff some reachable loop state does. -/
@[simp] theorem ran_iter (f : A → Eff (B ⊕ A)) (a : A) :
    (iter f a).ran = ∃ a', Reaches f a a' ∧ (f a').ran := rfl

/-- The underlying `Part`-valued arrow of an iteration. -/
theorem valFun_iter (f : A → Eff (B ⊕ A)) : valFun (iter f) = Elgot.iter (valFun f) := rfl

/-- A finite successful run is a reachable state that immediately returns. -/
theorem runs_iff_reaches (f : A → Eff (B ⊕ A)) (a : A) (b : B) :
    Part.Runs (valFun f) a b ↔ ∃ a', Reaches f a a' ∧ Sum.inl b ∈ (f a').val := by
  constructor
  · intro h
    induction h with
    | done hs => exact ⟨_, .refl _, hs⟩
    | more hs _ ih =>
        obtain ⟨a', hr, hb⟩ := ih
        exact ⟨a', .step hs hr, hb⟩
  · rintro ⟨a', hr, hb⟩
    revert hb
    induction hr with
    | refl _ => exact fun hb ↦ .done hb
    | step hs _ ih => exact fun hb ↦ .more hs (ih hb)

/-! ## The Elgot laws -/

/-- The fixpoint law. -/
theorem fixpoint (f : A → Eff (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply Eff.ext
  · have hb : (fun s : B ⊕ A ↦ (Sum.elim (pure : B → Eff B) (iter f) s).val)
        = Sum.elim pure (Elgot.iter (valFun f)) := by
      funext s; cases s <;> rfl
    change Elgot.iter (valFun f) a
      = (f a).val >>= fun s ↦ (Sum.elim (pure : B → Eff B) (iter f) s).val
    rw [hb]
    exact congrFun (Part.fixpoint (valFun f)) a
  · apply propext
    constructor
    · rintro ⟨a', hr, hran⟩
      cases hr with
      | refl _ => exact Or.inl hran
      | step hs ht => exact Or.inr ⟨Sum.inr _, hs, ⟨a', ht, hran⟩⟩
    · rintro (h | ⟨s, hs, hran⟩)
      · exact ⟨a, .refl a, h⟩
      · cases s with
        | inl b => exact hran.elim
        | inr a₁ =>
            obtain ⟨a', hr, hb⟩ := hran
            exact ⟨a', .step hs hr, hb⟩

/-! ### Naturality -/

/-- `mapReturn` commutes with taking partial values. -/
theorem val_mapReturn (f : A → Eff (B ⊕ A)) (g : B → Eff C) :
    valFun (mapReturn f g) = mapReturn (valFun f) (valFun g) := by
  funext a
  have hfun : (fun s : B ⊕ A ↦
        (Sum.elim (fun b ↦ g b >>= (pure ∘ Sum.inl))
          ((pure : C ⊕ A → Eff (C ⊕ A)) ∘ Sum.inr) s).val)
      = Sum.elim (fun b ↦ valFun g b >>= (pure ∘ Sum.inl)) (pure ∘ Sum.inr) := by
    funext s; cases s <;> rfl
  exact congrArg (fun k ↦ (f a).val >>= k) hfun

/-- `mapReturn f g` performs an effect at `a` iff `f` does, or `f` returns a value at
which `g` does. -/
theorem ran_mapReturn (f : A → Eff (B ⊕ A)) (g : B → Eff C) (a : A) :
    (mapReturn f g a).ran ↔ (f a).ran ∨ ∃ b, Sum.inl b ∈ (f a).val ∧ (g b).ran := by
  constructor
  · rintro (h | ⟨s, hs, hran⟩)
    · exact Or.inl h
    · cases s with
      | inl b =>
          rcases hran with h | ⟨_, _, hc⟩
          · exact Or.inr ⟨b, hs, h⟩
          · exact hc.elim
      | inr a' => exact hran.elim
  · rintro (h | ⟨b, hb, hg⟩)
    · exact Or.inl h
    · exact Or.inr ⟨Sum.inl b, hb, Or.inl hg⟩

/-- `mapReturn` does not change the recursive calls of a loop body. -/
theorem mem_inr_mapReturn_iff (f : A → Eff (B ⊕ A)) (g : B → Eff C) (a a' : A) :
    Sum.inr a' ∈ (mapReturn f g a).val ↔ Sum.inr a' ∈ (f a).val := by
  rw [show (mapReturn f g a).val = mapReturn (valFun f) (valFun g) a from
        congrFun (val_mapReturn f g) a, Part.mem_mapReturn_iff]
  constructor
  · rintro (⟨_, _, _, _, h⟩ | ⟨a₂, h, h2⟩)
    · cases h
    · have ha : a' = a₂ := Sum.inr.inj h2
      subst ha
      exact h
  · intro h
    exact Or.inr ⟨a', h, rfl⟩

/-- `mapReturn` does not change which loop states are reachable. -/
theorem reaches_mapReturn (f : A → Eff (B ⊕ A)) (g : B → Eff C) {a a' : A} :
    Reaches (mapReturn f g) a a' ↔ Reaches f a a' :=
  ⟨Reaches.mono (fun a a' hs ↦ (mem_inr_mapReturn_iff f g a a').mp hs),
    Reaches.mono (fun a a' hs ↦ (mem_inr_mapReturn_iff f g a a').mpr hs)⟩

/-- The naturality law. -/
theorem naturality (f : A → Eff (B ⊕ A)) (g : B → Eff C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  apply Eff.ext
  · change Elgot.iter (valFun f) a >>= valFun g = Elgot.iter (valFun (mapReturn f g)) a
    rw [val_mapReturn]
    exact congrFun (Part.naturality (valFun f) (valFun g)) a
  · apply propext
    constructor
    · rintro (⟨a', hr, hran⟩ | ⟨b, hb, hg⟩)
      · exact ⟨a', (reaches_mapReturn f g).mpr hr, (ran_mapReturn f g a').mpr (Or.inl hran)⟩
      · rw [val_iter, Part.mem_iter_iff] at hb
        obtain ⟨a', hr, hbmem⟩ := (runs_iff_reaches f a b).mp hb
        exact ⟨a', (reaches_mapReturn f g).mpr hr,
          (ran_mapReturn f g a').mpr (Or.inr ⟨b, hbmem, hg⟩)⟩
    · rintro ⟨a', hr, hran⟩
      have hr' := (reaches_mapReturn f g).mp hr
      rcases (ran_mapReturn f g a').mp hran with h | ⟨b, hbmem, hg⟩
      · exact Or.inl ⟨a', hr', h⟩
      · refine Or.inr ⟨b, ?_, hg⟩
        rw [val_iter, Part.mem_iter_iff]
        exact (runs_iff_reaches f a b).mpr ⟨a', hr', hbmem⟩

/-! ### Codiagonal -/

/-- `flattenBody` commutes with taking partial values. -/
theorem val_flattenBody (f : A → Eff ((B ⊕ A) ⊕ A)) :
    valFun (flattenBody f) = flattenBody (valFun f) := rfl

/-- `flattenBody` performs exactly the effects of the body it flattens. -/
theorem ran_flattenBody (f : A → Eff ((B ⊕ A) ⊕ A)) (a : A) :
    (flattenBody f a).ran ↔ (f a).ran := by
  constructor
  · rintro (h | ⟨_, _, h⟩)
    · exact h
    · exact h.elim
  · exact Or.inl

/-- The recursive calls of a flattened body are the recursive calls of either loop. -/
theorem mem_inr_flattenBody_iff (f : A → Eff ((B ⊕ A) ⊕ A)) (a a' : A) :
    Sum.inr a' ∈ (flattenBody f a).val ↔
      Sum.inl (Sum.inr a') ∈ (f a).val ∨ Sum.inr a' ∈ (f a).val := by
  rw [show (flattenBody f a).val = flattenBody (valFun f) a from
        congrFun (val_flattenBody f) a, Part.mem_flattenBody_iff]
  constructor
  · rintro ⟨x, hx, hf⟩
    simp only [flatten] at hf
    cases x with
    | inl s =>
        cases s with
        | inl b => cases hf
        | inr a₂ =>
            have ha : a₂ = a' := Sum.inr.inj hf
            subst ha
            exact Or.inl hx
    | inr a₂ =>
        have ha : a₂ = a' := Sum.inr.inj hf
        subst ha
        exact Or.inr hx
  · rintro (h | h)
    · exact ⟨Sum.inl (Sum.inr a'), h, rfl⟩
    · exact ⟨Sum.inr a', h, rfl⟩

/-- Every state reachable by the inner loop is reachable by the flattened one. -/
theorem Reaches.toFlattenBody (f : A → Eff ((B ⊕ A) ⊕ A)) {a a' : A}
    (h : Reaches f a a') : Reaches (flattenBody f) a a' :=
  h.mono fun a a' hs ↦ (mem_inr_flattenBody_iff f a a').mpr (Or.inr hs)

/-- Every state reachable by the outer loop is reachable by the flattened one. -/
theorem Reaches.ofIter (f : A → Eff ((B ⊕ A) ⊕ A)) {a a' : A}
    (h : Reaches (iter f) a a') : Reaches (flattenBody f) a a' := by
  induction h with
  | refl a => exact .refl a
  | @step a a₁ _ hs _ ih =>
      rw [val_iter, Part.mem_iter_iff] at hs
      obtain ⟨a₂, hr, hmem⟩ := (runs_iff_reaches f a (Sum.inr a₁)).mp hs
      refine Reaches.trans (Reaches.trans hr.toFlattenBody ?_) ih
      exact .step ((mem_inr_flattenBody_iff f a₂ a₁).mpr (Or.inl hmem)) (.refl a₁)

/-- Conversely, a flattened run splits into outer steps followed by inner ones. -/
theorem reaches_iter_split (f : A → Eff ((B ⊕ A) ⊕ A)) {a a' : A}
    (h : Reaches (flattenBody f) a a') :
    ∃ a₁, Reaches (iter f) a a₁ ∧ Reaches f a₁ a' := by
  induction h with
  | refl a => exact ⟨a, .refl a, .refl a⟩
  | @step a a₂ _ hs _ ih =>
      obtain ⟨a₁, h1, h2⟩ := ih
      rcases (mem_inr_flattenBody_iff f a a₂).mp hs with hout | hin
      · refine ⟨a₁, .step ?_ h1, h2⟩
        rw [val_iter, Part.mem_iter_iff]
        exact .done hout
      · cases h1 with
        | refl _ => exact ⟨a, .refl a, .step hin h2⟩
        | @step _ a₃ _ hq hrest =>
            rw [val_iter, Part.mem_iter_iff] at hq
            refine ⟨a₁, .step ?_ hrest, h2⟩
            rw [val_iter, Part.mem_iter_iff]
            exact .more hin hq

/-- The codiagonal law. -/
theorem codiagonal (f : A → Eff ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply Eff.ext
  · change Elgot.iter (Elgot.iter (valFun f)) a = Elgot.iter (flattenBody (valFun f)) a
    exact congrFun (Part.codiagonal (valFun f)) a
  · apply propext
    constructor
    · rintro ⟨a₁, h1, a₂, h2, hran⟩
      exact ⟨a₂, (Reaches.ofIter f h1).trans h2.toFlattenBody,
        (ran_flattenBody f a₂).mpr hran⟩
    · rintro ⟨a', hr, hran⟩
      obtain ⟨a₁, h1, h2⟩ := reaches_iter_split f hr
      exact ⟨a₁, h1, a', h2, (ran_flattenBody f a').mp hran⟩

/-! ### Uniformity -/

/-- The uniformity law, for pure comparison maps. -/
theorem uniformity (f : A → Eff (B ⊕ A)) (g : C → Eff (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  have commVal : kcomp (valFun f) (liftPure (Sum.map id h)) = kcomp (liftPure h) (valFun g) := by
    funext a
    exact congrArg Eff.val (congrFun comm a)
  have commRan : ∀ a : A, (f a).ran ↔ (g (h a)).ran := by
    intro a
    constructor
    · intro hf
      have hx : (kcomp f (liftPure (Sum.map id h)) a).ran := Or.inl hf
      rw [congrFun comm a] at hx
      rcases hx with hc | ⟨c, hc, hg⟩
      · exact hc.elim
      · have hce : c = h a := _root_.Part.mem_some_iff.mp hc
        exact hce ▸ hg
    · intro hg
      have hx : (kcomp (liftPure h) g a).ran := Or.inr ⟨h a, _root_.Part.mem_some _, hg⟩
      rw [← congrFun comm a] at hx
      rcases hx with hf | ⟨_, _, hs⟩
      · exact hf
      · exact hs.elim
  have hstep : ∀ (a : A) (t : B ⊕ C),
      t ∈ (g (h a)).val ↔ ∃ s, s ∈ (f a).val ∧ Sum.map id h s = t :=
    Part.uniform_step (valFun f) (valFun g) h commVal
  have hfwd : ∀ {a a' : A}, Reaches f a a' → Reaches g (h a) (h a') := by
    intro a a' hr
    induction hr with
    | refl a => exact .refl _
    | step hs _ ih =>
        refine .step ?_ ih
        rw [hstep]
        exact ⟨Sum.inr _, hs, rfl⟩
  have hrev : ∀ {c c' : C}, Reaches g c c' → ∀ a : A, c = h a →
      ∃ a', Reaches f a a' ∧ c' = h a' := by
    intro c c' hr
    induction hr with
    | refl c => exact fun a ha ↦ ⟨a, .refl a, ha⟩
    | @step _ c₁ _ hs _ ih =>
        intro a ha
        subst ha
        rw [hstep] at hs
        obtain ⟨s, hsmem, hseq⟩ := hs
        cases s with
        | inl b => cases hseq
        | inr a₂ =>
            obtain ⟨a', hra, hc'⟩ := ih a₂ (Sum.inr.inj hseq).symm
            exact ⟨a', .step hsmem hra, hc'⟩
  funext a
  apply Eff.ext
  · exact congrFun (Part.uniformity (valFun f) (valFun g) h commVal) a
  · apply propext
    constructor
    · rintro ⟨a', hr, hran⟩
      exact Or.inr ⟨h a, _root_.Part.mem_some _, h a', hfwd hr, (commRan a').mp hran⟩
    · rintro (hc | ⟨c, hc, c', hr, hran⟩)
      · exact hc.elim
      · have hce : c = h a := _root_.Part.mem_some_iff.mp hc
        subst hce
        obtain ⟨a', hra, rfl⟩ := hrev hr a rfl
        exact ⟨a', hra, (commRan a').mpr hran⟩

/-- `Eff` is a complete Elgot monad. -/
noncomputable instance instLawfulElgotMonad : LawfulElgotMonad Eff where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

/-! ## The completeness counterexample

A loop whose body diverges silently and a loop whose body diverges after
performing an effect have the same (empty) partial value, but different effect
flags.  Since `Eff` is a lawful Elgot monad, no equation derivable in the
λ-iter equational theory can identify the two loops, even though every state
model makes them observationally indistinguishable. -/

/-- A purely diverging loop performs no effect. -/
@[simp] theorem iter_forever_pure (a : A) :
    iter (fun a ↦ (⟨_root_.Part.some (Sum.inr a), False⟩ : Eff (B ⊕ A))) a
      = ⟨_root_.Part.none, False⟩ := by
  apply Eff.ext
  · change Elgot.iter (fun a : A ↦ _root_.Part.some (Sum.inr a)) a = _root_.Part.none
    exact Part.iter_forever a
  · apply propext
    constructor
    · rintro ⟨_, _, hran⟩
      exact hran
    · exact False.elim

/-- A diverging loop whose body performs an effect does perform an effect. -/
@[simp] theorem iter_forever_effectful (a : A) :
    iter (fun a ↦ (⟨_root_.Part.some (Sum.inr a), True⟩ : Eff (B ⊕ A))) a
      = ⟨_root_.Part.none, True⟩ := by
  apply Eff.ext
  · change Elgot.iter (fun a : A ↦ _root_.Part.some (Sum.inr a)) a = _root_.Part.none
    exact Part.iter_forever a
  · apply propext
    constructor
    · exact fun _ ↦ trivial
    · exact fun _ ↦ ⟨a, .refl a, trivial⟩

/-- The two diverging loops are distinguished by `Eff`, although both have the
empty partial value. -/
theorem iter_forever_pure_ne_effectful (a : A) :
    iter (B := B) (fun a ↦ (⟨_root_.Part.some (Sum.inr a), False⟩ : Eff (B ⊕ A))) a ≠
      iter (B := B) (fun a ↦ (⟨_root_.Part.some (Sum.inr a), True⟩ : Eff (B ⊕ A))) a := by
  rw [iter_forever_pure, iter_forever_effectful]
  intro heq
  exact Eq.mp (congrArg Eff.ran heq).symm trivial

end Eff

end Isotope.Elgot
