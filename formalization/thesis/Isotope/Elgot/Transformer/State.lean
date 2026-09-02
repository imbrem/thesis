import Isotope.Elgot.Basic

/-!
# The state transformer preserves complete Elgot monads

`StateT S m A = S → m (A × S)`.  Iteration threads the state through every recursive step: the
loop over `A` in `StateT S m` becomes a loop over `A × S` in `m`.

## Coproduct orientation

The body of an iteration is `f : A → StateT S m (B ⊕ A)`, i.e. `A → S → m ((B ⊕ A) × S)`, while
`m`'s `iter` wants `X → m (Y ⊕ X)`.  Taking `X = A × S` and `Y = B × S` forces the distributor

  `distr : (B ⊕ A) × S → (B × S) ⊕ (A × S)`

which must send `Sum.inl` to `Sum.inl` and `Sum.inr` to `Sum.inr`, since `Sum.inl` is the returned
value (whose final state is the one `iter` must deliver) and `Sum.inr` is the recursive call (whose
state is the one fed to the next step).  Any other orientation would be ill-typed.

Unlike the writer transformer, the state loop starts from the *incoming* state, so no analogue of
the writer's `iter_shift` equivariance lemma is needed.

## Note on `iter_threaded`

`Isotope.CategoryTheory.Monad.Elgot.iter_threaded` threads a *constant* `Z` that the body never
reads; it is the left-whiskering/strength lemma.  `StateT`'s state is read and written at every
step, so that lemma does not apply here.  Its proof technique — uniformity along a pure map,
composed with naturality — is what is reused, in `codiagonal` below.
-/

namespace Isotope.Elgot.Transformer.State

universe u

variable {S : Type u} {m : Type u → Type u} {A B C : Type u}

/-- Distribute the state over the return/recurse coproduct: `Sum.inl` (return) stays `Sum.inl`,
`Sum.inr` (recurse) stays `Sum.inr`. -/
def distr : (B ⊕ A) × S → (B × S) ⊕ (A × S)
  | (Sum.inl b, s) => Sum.inl (b, s)
  | (Sum.inr a, s) => Sum.inr (a, s)

section

variable [Monad m]

/-- Uncurry a State-Kleisli arrow into an `m`-Kleisli arrow on the enlarged state space. -/
abbrev run' (f : A → StateT S m B) : A × S → m (B × S) := fun p ↦ f p.1 p.2

/-- The iteration body transported to `m`, with the state distributed over the coproduct. -/
abbrev body (f : A → StateT S m (B ⊕ A)) : A × S → m ((B × S) ⊕ (A × S)) :=
  fun p ↦ distr <$> run' f p

omit [Monad m] in
/-- State-Kleisli arrows with equal uncurryings are equal. -/
theorem ext_run' {F G : A → StateT S m B} (h : run' F = run' G) : F = G := by
  funext a s; exact congrFun h (a, s)

/-- Uncurrying is a homomorphism for Kleisli composition. -/
theorem kcomp_run' (f : A → StateT S m B) (g : B → StateT S m C) :
    run' (kcomp f g) = kcomp (run' f) (run' g) := rfl

/-- Uncurrying sends a pure Kleisli arrow to the pure Kleisli arrow of `Prod.map h id`: the
comparison map for uniformity must be enlarged along the state. -/
theorem liftPure_run' (h : A → B) :
    run' (liftPure (m := StateT S m) h) = liftPure (m := m) (Prod.map h id) := rfl

end

section

variable [Monad m] [Iterate m]

/-- Iteration in `StateT S m`, by threading the state through the recursive argument. -/
instance instIterate : Iterate (StateT S m) where
  iter f a s := iter (m := m) (body f) (a, s)

/-- The uncurrying of `iter f` is `m`'s iteration of the transported body: this is the
definition. -/
theorem iter_run' (f : A → StateT S m (B ⊕ A)) :
    run' (iter f) = iter (m := m) (body f) := rfl

end

section

variable [Monad m] [LawfulMonad m]

/-- Transporting the body commutes with postcomposition on the returned summand. -/
theorem mapReturn_body (f : A → StateT S m (B ⊕ A)) (g : B → StateT S m C) :
    mapReturn (m := m) (body f) (run' g) = body (mapReturn f g) := by
  funext p
  change (distr <$> run' f p) >>= _ = distr <$> (run' f p >>= _)
  rw [map_eq_pure_bind, bind_assoc, map_eq_pure_bind, bind_assoc]
  refine bind_congr fun q ↦ ?_
  obtain ⟨x, s⟩ := q
  cases x with
  | inl b =>
    simp only [pure_bind]
    change run' g (b, s) >>= (pure ∘ Sum.inl) = (g b s >>= _) >>= _
    rw [bind_assoc]
    refine bind_congr fun q ↦ ?_
    obtain ⟨c, s'⟩ := q
    change (pure (Sum.inl (c, s')) : m ((C × S) ⊕ (A × S)))
      = (pure (Sum.inl c, s') : m ((C ⊕ A) × S)) >>= (pure ∘ distr)
    rw [pure_bind]
    rfl
  | inr a =>
    simp only [pure_bind]
    change (pure (Sum.inr (a, s)) : m ((C × S) ⊕ (A × S)))
      = (pure (Sum.inr a, s) : m ((C ⊕ A) × S)) >>= (pure ∘ distr)
    rw [pure_bind]
    rfl

/-- Transporting a `flattenBody` unfolds to a single bind applying `distr ∘ flatten`. -/
theorem body_flattenBody (f : A → StateT S m ((B ⊕ A) ⊕ A)) (p : A × S) :
    body (flattenBody f) p = run' f p >>= fun q ↦ pure (distr (flatten q.1, q.2)) := by
  change distr <$> (run' f p >>= fun q ↦ (pure (flatten q.1) : StateT S m (B ⊕ A)) q.2) = _
  rw [map_eq_pure_bind, bind_assoc]
  refine bind_congr fun q ↦ ?_
  change (pure (flatten q.1, q.2) : m ((B ⊕ A) × S)) >>= (fun a ↦ pure (distr a)) = _
  rw [pure_bind]

/-- `flattenBody` commutes with the transport, once the outer `distr` has been absorbed. -/
theorem flattenBody_body (f : A → StateT S m ((B ⊕ A) ⊕ A)) :
    flattenBody (m := m) (mapReturn (m := m) (body f) (liftPure (m := m) distr))
      = body (flattenBody f) := by
  funext p
  rw [body_flattenBody]
  simp only [flattenBody, mapReturn, kcomp, liftPure, Function.comp_def, body, run',
    map_eq_pure_bind, bind_assoc, pure_bind]
  refine bind_congr fun q ↦ ?_
  obtain ⟨y, s⟩ := q
  cases y with
  | inl z => cases z <;> simp [distr, flatten]
  | inr a => simp [distr, flatten]

end

section

variable [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

/-- The Elgot fixpoint law for `StateT S m`. -/
theorem fixpoint (f : A → StateT S m (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  refine ext_run' ?_
  rw [iter_run', LawfulElgotMonad.fixpoint (m := m) (body f)]
  funext p
  change (distr <$> run' f p) >>= Sum.elim pure (iter (m := m) (body f))
      = run' f p >>= fun q ↦ (Sum.elim pure (iter f) q.1 : StateT S m B) q.2
  rw [map_eq_pure_bind, bind_assoc]
  refine bind_congr fun q ↦ ?_
  rw [pure_bind]
  obtain ⟨x, s⟩ := q
  cases x <;> rfl

/-- Naturality for `StateT S m`. -/
theorem naturality (f : A → StateT S m (B ⊕ A)) (g : B → StateT S m C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  refine ext_run' ?_
  rw [kcomp_run', iter_run', iter_run', LawfulElgotMonad.naturality (m := m), mapReturn_body]

omit [LawfulElgotMonad m] in
/-- The body of an iterated iteration is not itself an iteration but a *postcomposition* of one
with `distr`; this is the step that forces naturality to be used before codiagonality. -/
theorem body_iter (f : A → StateT S m ((B ⊕ A) ⊕ A)) :
    body (iter f) = kcomp (m := m) (iter (m := m) (body f)) (liftPure (m := m) distr) := by
  funext p
  exact map_eq_pure_bind distr (iter (m := m) (body f) p)

/-- The codiagonal law for `StateT S m`. -/
theorem codiagonal (f : A → StateT S m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  refine ext_run' ?_
  rw [iter_run', iter_run', body_iter, LawfulElgotMonad.naturality (m := m),
    LawfulElgotMonad.codiagonal (m := m), flattenBody_body]

/-- Pure uniformity for `StateT S m`: the comparison map `h : A → C` is enlarged to
`Prod.map h id : A × S → C × S`. -/
theorem uniformity (f : A → StateT S m (B ⊕ A)) (g : C → StateT S m (B ⊕ C))
    (h : A → C) (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  refine ext_run' ?_
  rw [iter_run', kcomp_run', liftPure_run', iter_run']
  refine LawfulElgotMonad.uniformity (m := m) (body f) (body g) (Prod.map h id) ?_
  have hc := congrArg (run' (S := S)) comm
  rw [kcomp_run', kcomp_run', liftPure_run', liftPure_run'] at hc
  funext p
  have hcp := congrFun hc p
  simp only [kcomp, liftPure, Function.comp_def, body, run', map_eq_pure_bind,
    bind_assoc, pure_bind] at hcp ⊢
  rw [← hcp, bind_assoc]
  refine bind_congr fun q ↦ ?_
  rw [pure_bind]
  obtain ⟨x, s⟩ := q
  cases x <;> rfl

/-- `StateT S m` is a complete Elgot monad whenever `m` is. -/
instance instLawfulElgotMonad : LawfulElgotMonad (StateT S m) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end

end Isotope.Elgot.Transformer.State
