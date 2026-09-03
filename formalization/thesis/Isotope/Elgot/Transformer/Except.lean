import Isotope.Elgot.Basic

/-! # The exception transformer preserves complete Elgot monads -/

namespace Isotope.Elgot.Transformer.Except

universe u

variable {E m A B C : Type u} {m : Type u → Type u}

/-- Exceptions are terminal results, while successful recursive requests remain recursive. -/
def distr : Except E (B ⊕ A) → Except E B ⊕ A
  | .error e => .inl (.error e)
  | .ok (.inl b) => .inl (.ok b)
  | .ok (.inr a) => .inr a

section

variable [Monad m]

def run' (f : A → ExceptT E m B) : A → m (Except E B) := fun a => (f a).run

def handle (g : B → ExceptT E m C) : Except E B → m (Except E C)
  | .error e => pure (.error e)
  | .ok b => (g b).run

def body (f : A → ExceptT E m (B ⊕ A)) : A → m (Except E B ⊕ A) :=
  fun a => distr <$> run' f a

omit [Monad m] in
theorem ext_run' {f g : A → ExceptT E m B} (h : run' f = run' g) : f = g := by
  funext a
  apply ExceptT.ext
  exact congrFun h a

theorem kcomp_run' (f : A → ExceptT E m B) (g : B → ExceptT E m C) :
    run' (kcomp f g) = kcomp (run' f) (handle g) := by
  funext a
  change (f a).run >>= ExceptT.bindCont g = (f a).run >>= handle g
  refine bind_congr fun x => ?_
  cases x <;> rfl

theorem liftPure_run' (h : A → B) :
    run' (liftPure (m := ExceptT E m) h) = liftPure (m := m) (.ok ∘ h) := by
  rfl

end

section

variable [Monad m] [Iterate m]

instance instIterate : Iterate (ExceptT E m) where
  iter f := iter (m := m) (body f)

theorem iter_run' (f : A → ExceptT E m (B ⊕ A)) :
    run' (iter (m := ExceptT E m) f) = iter (m := m) (body f) := rfl

end

section

variable [Monad m] [LawfulMonad m]

theorem mapReturn_body (f : A → ExceptT E m (B ⊕ A)) (g : B → ExceptT E m C) :
    mapReturn (m := m) (body f) (handle g) = body (mapReturn f g) := by
  funext a
  change (distr <$> run' f a) >>= _ = distr <$> (run' f a >>= _)
  rw [map_eq_pure_bind, bind_assoc, map_eq_pure_bind, bind_assoc]
  refine bind_congr fun x => ?_
  cases x with
  | error e => simp [distr, handle, ExceptT.bindCont]
  | ok x => cases x with
    | inl b =>
      rw [pure_bind]
      simp only [distr, Sum.elim_inl, handle, ExceptT.bindCont]
      change (g b).run >>= (pure ∘ Sum.inl) =
        ((g b).run >>= ExceptT.bindCont (pure ∘ Sum.inl)) >>= fun y => pure (distr y)
      rw [bind_assoc]
      refine bind_congr fun y => ?_
      cases y with
      | error e =>
        simp only [ExceptT.bindCont, Function.comp_apply]
        rw [pure_bind]
        rfl
      | ok c =>
        change (pure (Sum.inl (Except.ok c)) : m (Except E C ⊕ A)) =
          (pure (Except.ok (Sum.inl c)) : m (Except E (C ⊕ A))) >>= fun z => pure (distr z)
        rw [pure_bind]
        rfl
    | inr a =>
      rw [pure_bind]
      simp only [distr, Sum.elim_inr, handle, ExceptT.bindCont, map_eq_pure_bind,
        pure_bind]
      change (pure (Sum.inr a) : m (Except E C ⊕ A)) =
        (pure (Except.ok (Sum.inr a)) : m (Except E (C ⊕ A))) >>= fun z => pure (distr z)
      rw [pure_bind]
      rfl

theorem body_flattenBody (f : A → ExceptT E m ((B ⊕ A) ⊕ A)) (a : A) :
    body (flattenBody f) a = run' f a >>= fun x => pure (distr (Except.map flatten x)) := by
  change distr <$> ((flattenBody f a).run) = _
  change distr <$> ((f a).run >>= ExceptT.bindCont (pure ∘ flatten)) = _
  rw [map_eq_pure_bind, bind_assoc]
  refine bind_congr fun x => ?_
  cases x with
  | error e =>
    simp only [ExceptT.bindCont, Except.map]
    rw [pure_bind]
  | ok x =>
    simp only [ExceptT.bindCont, Function.comp_apply, Except.map]
    change (pure (Except.ok (flatten x)) : m (Except E (B ⊕ A))) >>= (fun z =>
      (pure (distr z) : m (Except E B ⊕ A))) =
      (pure (distr (Except.ok (flatten x))) : m (Except E B ⊕ A))
    rw [pure_bind]

theorem flattenBody_body (f : A → ExceptT E m ((B ⊕ A) ⊕ A)) :
    flattenBody (m := m)
      (mapReturn (m := m) (body f) (liftPure (m := m) distr)) =
      body (flattenBody f) := by
  funext a
  rw [body_flattenBody]
  simp only [flattenBody, mapReturn, kcomp, liftPure, Function.comp_def, body, run',
    map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro x
  cases x with
  | error e => simp [distr, flatten, Except.map]
  | ok x => cases x with
    | inl x => cases x <;> simp [distr, flatten, Except.map]
    | inr a => simp [distr, flatten, Except.map]

end

section

variable [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

theorem fixpoint (f : A → ExceptT E m (B ⊕ A)) :
    iter (m := ExceptT E m) f = fun a =>
      f a >>= Sum.elim pure (iter (m := ExceptT E m) f) := by
  refine ext_run' ?_
  change iter (body f) = kcomp (m := m) f
    (ExceptT.bindCont (Sum.elim (fun b => (pure (Except.ok b) : m (Except E B)))
      (iter (m := m) (body f))))
  rw [LawfulElgotMonad.fixpoint (m := m) (body f)]
  funext a
  simp only [body, run', map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro x
  cases x with
  | error e => simp [distr, ExceptT.bindCont]
  | ok x => cases x with
    | inl b => simp [distr, ExceptT.bindCont]
    | inr a =>
      simp only [distr, ExceptT.bindCont, pure_bind, Sum.elim_inr]
      rw [congrFun (LawfulElgotMonad.fixpoint (m := m) (body f)) a]
      change (distr <$> run' f a) >>= _ = _
      rw [map_eq_pure_bind, bind_assoc]
      refine bind_congr fun x => ?_
      rw [pure_bind]
      cases x <;> rfl

theorem naturality (f : A → ExceptT E m (B ⊕ A)) (g : B → ExceptT E m C) :
    kcomp (iter (m := ExceptT E m) f) g =
      iter (m := ExceptT E m) (mapReturn f g) := by
  refine ext_run' ?_
  rw [kcomp_run', iter_run', iter_run', LawfulElgotMonad.naturality (m := m), mapReturn_body]

theorem body_iter (f : A → ExceptT E m ((B ⊕ A) ⊕ A)) :
    body (iter (m := ExceptT E m) f) =
      kcomp (m := m) (iter (m := m) (body f)) (liftPure (m := m) distr) := by
  funext a
  exact map_eq_pure_bind distr (iter (m := m) (body f) a)

theorem codiagonal (f : A → ExceptT E m ((B ⊕ A) ⊕ A)) :
    iter (m := ExceptT E m) (iter (m := ExceptT E m) f) =
      iter (m := ExceptT E m) (flattenBody f) := by
  refine ext_run' ?_
  rw [iter_run', iter_run', body_iter, LawfulElgotMonad.naturality (m := m),
    LawfulElgotMonad.codiagonal (m := m), flattenBody_body]

theorem uniformity (f : A → ExceptT E m (B ⊕ A))
    (g : C → ExceptT E m (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter (m := ExceptT E m) f =
      kcomp (liftPure h) (iter (m := ExceptT E m) g) := by
  refine ext_run' ?_
  rw [iter_run', kcomp_run', liftPure_run']
  funext a
  change iter (m := m) (body f) a = pure (Except.ok (h a)) >>= handle (iter g)
  rw [pure_bind]
  change iter (m := m) (body f) a = iter (m := m) (body g) (h a)
  suffices hu : iter (m := m) (body f) = kcomp (liftPure h) (iter (body g)) by
    simpa [kcomp, liftPure, Function.comp_def] using congrFun hu a
  refine LawfulElgotMonad.uniformity (m := m) (body f) (body g) h ?_
  funext a
  have hc := congrFun comm a
  simp only [kcomp, liftPure, Function.comp_def, body, run', map_eq_pure_bind,
    bind_assoc, pure_bind] at hc ⊢
  rw [← hc]
  change (run' f a >>= fun x => pure (Sum.map id h (distr x))) =
    ((f a).run >>= ExceptT.bindCont (pure ∘ Sum.map id h)) >>= fun y => pure (distr y)
  rw [bind_assoc]
  apply bind_congr
  intro x
  cases x with
  | error e =>
    simp only [ExceptT.bindCont, Function.comp_apply]
    rw [pure_bind]
    rfl
  | ok x => cases x with
    | inl b =>
      change (pure (Sum.inl (Except.ok b)) : m (Except E B ⊕ C)) =
        (pure (Except.ok (Sum.inl b)) : m (Except E (B ⊕ C))) >>= fun z => pure (distr z)
      rw [pure_bind]
      rfl
    | inr a =>
      change (pure (Sum.inr (h a)) : m (Except E B ⊕ C)) =
        (pure (Except.ok (Sum.inr (h a))) : m (Except E (B ⊕ C))) >>= fun z => pure (distr z)
      rw [pure_bind]
      rfl

instance instLawfulElgotMonad : LawfulElgotMonad (ExceptT E m) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end

end Isotope.Elgot.Transformer.Except
