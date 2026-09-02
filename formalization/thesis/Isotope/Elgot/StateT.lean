import Isotope.Elgot.Basic

/-!
# The state monad transformer preserves Elgot structure

If `m` is a (complete) Elgot monad, then so is `StateT S m`.  The construction is
the evident one: an iteration body `f : A → StateT S m (B ⊕ A)`, which after
uncurrying is a map `A × S → m ((B ⊕ A) × S)`, is turned into a genuine `m`-level
iteration body `A × S → m ((B × S) ⊕ (A × S))` by distributing the state
component over the sum, and `iter` is transported along this correspondence.

All four Conway/complete-Elgot laws transport.  The restriction of uniformity to
*pure* comparison maps is exactly what makes the last one work: a comparison map
`h : A → C` transports to `Prod.map h id : A × S → C × S`, which is again an
ordinary function, so the uniformity law of `m` applies to it.

Specializing to `m := Part` (which is a `LawfulElgotMonad` by
`Isotope.Elgot.Basic`) yields `Iterate (StateT S Part)` and
`LawfulElgotMonad (StateT S Part)`, the operational model of `λ_iter`.

Note that `StateT S m A` unfolds to `S → m (A × S)`: the *value* comes first and
the *state* second in the returned pair.
-/

namespace Isotope.Elgot

universe u

namespace StateT

variable {S : Type u} {m : Type u → Type u} {A B C : Type u}

/-! ### The transported iteration body -/

/-- Distribute the state component of an iteration body's result over the sum. -/
def distrib (S : Type u) {A B : Type u} : (B ⊕ A) × S → (B × S) ⊕ (A × S) :=
  fun q ↦ Sum.elim (fun b ↦ Sum.inl (b, q.2)) (fun a ↦ Sum.inr (a, q.2)) q.1

/-- Uncurry a Kleisli arrow of `StateT S m` into a Kleisli arrow of `m`. -/
def flat (f : A → _root_.StateT S m B) : A × S → m (B × S) := fun p ↦ f p.1 p.2

/-- The `m`-level iteration body associated to a `StateT S m` iteration body. -/
def body [Monad m] (f : A → _root_.StateT S m (B ⊕ A)) :
    A × S → m ((B × S) ⊕ (A × S)) :=
  fun p ↦ f p.1 p.2 >>= fun q ↦ pure (distrib S q)

/-- Iteration in `StateT S m`, transported from iteration in `m` along `body`. -/
instance instIterate [Monad m] [Iterate m] : Iterate (_root_.StateT S m) where
  iter f a s := Elgot.iter (body f) (a, s)

/-! ### Computation rules -/

/-- Applying a `StateT` bind to a state pushes the application inside. -/
theorem bind_apply [Monad m] (x : _root_.StateT S m B) (g : B → _root_.StateT S m C)
    (s : S) : (x >>= g) s = x s >>= fun p ↦ g p.1 p.2 := rfl

/-- Applying a `StateT` `pure` to a state pairs the value with the state. -/
theorem pure_apply [Monad m] (b : B) (s : S) :
    (pure b : _root_.StateT S m B) s = pure (b, s) := rfl

/-- `flat` turns `StateT` Kleisli composition into `m` Kleisli composition. -/
theorem flat_bind [Monad m] (x : A → _root_.StateT S m B)
    (g : B → _root_.StateT S m C) (p : A × S) :
    flat (fun a ↦ x a >>= g) p = flat x p >>= flat g := rfl

/-- The defining equation of `StateT` iteration. -/
theorem flat_iter [Monad m] [Iterate m] (f : A → _root_.StateT S m (B ⊕ A)) :
    flat (iter f) = Elgot.iter (body f) := rfl

/-- `body` is the pure post-composition of `flat` with `distrib`. -/
theorem body_eq [Monad m] (f : A → _root_.StateT S m (B ⊕ A)) :
    body f = kcomp (flat f) (liftPure (distrib S)) := rfl

/-! ### Transporting the Elgot laws -/

/-- `body` intertwines `mapReturn` in `StateT S m` with `mapReturn` in `m`. -/
theorem body_mapReturn [Monad m] [LawfulMonad m]
    (f : A → _root_.StateT S m (B ⊕ A)) (g : B → _root_.StateT S m C) :
    body (mapReturn f g) = mapReturn (body f) (flat g) := by
  funext p
  obtain ⟨a, s⟩ := p
  simp only [body, mapReturn, bind_apply, bind_assoc, pure_bind, flat, Function.comp_def]
  congr 1
  funext q
  obtain ⟨q1, s'⟩ := q
  cases q1 <;>
    simp only [Sum.elim_inl, Sum.elim_inr, bind_apply, pure_apply, bind_assoc, pure_bind,
      distrib]

/-- The fixpoint law transports along `body`. -/
theorem fixpoint [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
    (f : A → _root_.StateT S m (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a s
  change Elgot.iter (body f) (a, s) = _
  rw [LawfulElgotMonad.fixpoint (body f)]
  change (f a s >>= fun q ↦ pure (distrib S q)) >>= _ = _
  rw [bind_assoc]
  change _ = f a s >>= fun q ↦ (Sum.elim pure (iter f) q.1) q.2
  congr 1
  funext q
  obtain ⟨q1, s'⟩ := q
  cases q1 <;> simp [distrib] <;> rfl

/-- The naturality law transports along `body`. -/
theorem naturality [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
    (f : A → _root_.StateT S m (B ⊕ A)) (g : B → _root_.StateT S m C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  have h : kcomp (Elgot.iter (body f)) (flat g) = Elgot.iter (body (mapReturn f g)) := by
    rw [body_mapReturn]
    exact LawfulElgotMonad.naturality _ _
  funext a s
  exact congrFun h (a, s)

/-- The body of an iterated `StateT` loop, expressed at the level of `m`. -/
theorem body_iter [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
    (f : A → _root_.StateT S m ((B ⊕ A) ⊕ A)) :
    body (iter f) = Elgot.iter (mapReturn (body f) (liftPure (distrib S))) := by
  rw [body_eq, flat_iter]
  exact LawfulElgotMonad.naturality _ _

/-- `body` intertwines `flattenBody` in `StateT S m` with the flattened, retyped
body at the level of `m`. -/
theorem body_flattenBody [Monad m] [LawfulMonad m]
    (f : A → _root_.StateT S m ((B ⊕ A) ⊕ A)) :
    body (flattenBody f) =
      flattenBody (mapReturn (body f) (liftPure (distrib S))) := by
  funext p
  obtain ⟨a, s⟩ := p
  simp only [body, flattenBody, mapReturn, kcomp, liftPure, bind_apply, bind_assoc,
    pure_bind, Function.comp_def]
  congr 1
  funext r
  obtain ⟨r1, s'⟩ := r
  cases r1 <;>
    simp only [Sum.elim_inl, Sum.elim_inr, pure_apply, pure_bind, distrib, flatten, id_eq]

/-- The codiagonal law transports along `body`. -/
theorem codiagonal [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
    (f : A → _root_.StateT S m ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  have h : Elgot.iter (body (iter f)) = Elgot.iter (body (flattenBody f)) := by
    rw [body_iter, body_flattenBody, LawfulElgotMonad.codiagonal]
  funext a s
  exact congrFun h (a, s)

/-- The uniformity law transports along `body`, with the comparison map `h`
transported to the still-pure map `Prod.map h id`. -/
theorem uniformity [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]
    (f : A → _root_.StateT S m (B ⊕ A)) (g : C → _root_.StateT S m (B ⊕ C))
    (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  have comm' : ∀ (a : A) (s : S),
      (f a s >>= fun r ↦ (pure (Sum.map id h r.1, r.2) : m ((B ⊕ C) × S))) = g (h a) s := by
    intro a s
    have := congrFun (congrFun comm a) s
    simpa only [kcomp, liftPure, bind_apply, pure_apply, pure_bind, Function.comp_def]
      using this
  have mcomm : kcomp (body f) (liftPure (Sum.map id (Prod.map h (id : S → S)))) =
      kcomp (liftPure (Prod.map h (id : S → S))) (body g) := by
    funext p
    obtain ⟨a, s⟩ := p
    simp only [kcomp, liftPure, body, bind_assoc, pure_bind, Function.comp_def, Prod.map]
    rw [← comm']
    rw [bind_assoc]
    congr 1
    funext r
    obtain ⟨r1, s'⟩ := r
    cases r1 <;> simp only [pure_bind, distrib, Sum.elim_inl, Sum.elim_inr, Sum.map_inl,
      Sum.map_inr, id_eq, Prod.map]
  have key := LawfulElgotMonad.uniformity (body f) (body g)
    (Prod.map h (id : S → S)) mcomm
  funext a s
  have := congrFun key (a, s)
  simpa only [kcomp, liftPure, Function.comp_def, pure_bind, Prod.map, id_eq,
    bind_apply, pure_apply] using this

/-- The state monad transformer preserves the complete Elgot laws. -/
instance instLawfulElgotMonad [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m] :
    LawfulElgotMonad (_root_.StateT S m) where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end StateT

/-! ### The operational model: `StateT S Part`

These are the instances the operational semantics of `λ_iter` runs in.  They are
found by instance synthesis from `StateT.instIterate`, `StateT.instLawfulElgotMonad`
and the `Part` instances of `Isotope.Elgot.Basic`; the `example`s below record
that fact, and that `StateT S Part` has the shape `Type u → Type u` required by
`Isotope.LambdaIter.Semantics.denote`. -/

/-- Partial, deterministic state transformers over an abstract state set `S`.
This is the monad in which the operational semantics of `λ_iter` lives.

It is a `reducible` abbreviation for `StateT S Part`, provided mainly because
writing `StateT S Part` where a `Type v → Type v` is expected leaves Lean unable
to solve the resulting universe constraints; use `PartState S`, or else write
`StateT.{v, v} S Part.{v}` with explicit universe arguments. -/
abbrev PartState (S : Type u) : Type u → Type u := _root_.StateT S _root_.Part

example {S : Type u} : Type u → Type u := _root_.StateT.{u, u} S _root_.Part.{u}

example {S : Type u} : Monad (PartState S) := inferInstance

example {S : Type u} : LawfulMonad (PartState S) := inferInstance

noncomputable example {S : Type u} : Iterate (PartState S) := inferInstance

example {S : Type u} : LawfulElgotMonad (PartState S) := inferInstance

example {S : Type u} : Monad (_root_.StateT.{u, u} S _root_.Part.{u}) := inferInstance

example {S : Type u} : LawfulMonad (_root_.StateT.{u, u} S _root_.Part.{u}) := inferInstance

noncomputable example {S : Type u} : Iterate (_root_.StateT.{u, u} S _root_.Part.{u}) :=
  inferInstance

example {S : Type u} : LawfulElgotMonad (_root_.StateT.{u, u} S _root_.Part.{u}) :=
  inferInstance

end Isotope.Elgot
