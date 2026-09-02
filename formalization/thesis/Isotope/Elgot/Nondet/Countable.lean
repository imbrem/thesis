import Isotope.Elgot.Nondet.Powerset
import Mathlib.Data.Set.Countable

/-!
# Countable nondeterminism as a complete Elgot monad

`CSet A = {s : Set A // s.Countable}` is the countable-powerset monad.  Unlike the finite
powerset it *is* closed under reachability iteration: a countably-branching body reaches, at
each finite depth, a countable set of values, and a countable union of countable sets is
countable.  Every Elgot law then transfers from `Set` along the (injective, structure-preserving)
carrier map.

## Choice

`Set.countable_iUnion` and `Set.Countable.biUnion` pick injections `↥(t i) ↪ ℕ` uniformly in `i`,
i.e. they use countable choice; in Lean this is discharged by `Classical.choice`, which Mathlib
uses pervasively.  No *new* axiom is introduced: `#print axioms` on the instances below reports
exactly `propext`, `Classical.choice`, `Quot.sound`.  By contrast the `Set` development in
`Isotope.Elgot.Nondet.Powerset` needs no choice at all.
-/

namespace Isotope.Elgot.Nondet

universe u

variable {A B C : Type u}

/-! ### Bounded-depth reachability

`Runs` is an unbounded existential, so countability is proved by stratifying it by depth.
-/

section

/-- Values reachable from `a` by a successful run of depth at most `n`. -/
def RunsIn (f : A → Set (B ⊕ A)) : ℕ → A → Set B
  | 0, a => Sum.inl ⁻¹' f a
  | n + 1, a => (Sum.inl ⁻¹' f a) ∪ ⋃ a' ∈ (Sum.inr ⁻¹' f a), RunsIn f n a'

/-- Reachability is bounded reachability at some depth. -/
theorem runs_iff_exists_runsIn (f : A → Set (B ⊕ A)) (a : A) (b : B) :
    Runs f a b ↔ ∃ n, b ∈ RunsIn f n a := by
  constructor
  · intro h
    induction h with
    | done hs => exact ⟨0, hs⟩
    | more hs _ ih =>
        rcases ih with ⟨n, hn⟩
        exact ⟨n + 1, Or.inr (Set.mem_biUnion hs hn)⟩
  · rintro ⟨n, hn⟩
    induction n generalizing a with
    | zero => exact .done hn
    | succ n ih =>
        rcases hn with hn | hn
        · exact .done hn
        · rcases Set.mem_iUnion₂.mp hn with ⟨a', ha', hb⟩
          exact .more ha' (ih a' hb)

/-- A countably-branching body reaches countably many values at each finite depth. -/
theorem runsIn_countable {f : A → Set (B ⊕ A)} (hf : ∀ a, (f a).Countable) :
    ∀ (n : ℕ) (a : A), (RunsIn f n a).Countable := by
  intro n
  induction n with
  | zero => exact fun a ↦ (hf a).preimage Sum.inl_injective
  | succ n ih =>
      intro a
      exact ((hf a).preimage Sum.inl_injective).union
        (((hf a).preimage Sum.inr_injective).biUnion fun a' _ ↦ ih a')

/-- **Countable branching is closed under reachability.**  This is where countable choice is
used, via `Set.countable_iUnion` over the depth index. -/
theorem runs_countable {f : A → Set (B ⊕ A)} (hf : ∀ a, (f a).Countable) (a : A) :
    {b | Runs f a b}.Countable := by
  have h : {b | Runs f a b} = ⋃ n : ℕ, RunsIn f n a := by
    apply Set.ext
    intro b
    simpa using runs_iff_exists_runsIn f a b
  rw [h]
  exact Set.countable_iUnion fun n ↦ runsIn_countable hf n a

end

/-! ### The countable powerset monad -/

/-- Countably-branching nondeterminism, as an endofunctor of `Type u`. -/
def CSet (A : Type u) : Type u := {s : Set A // s.Countable}

namespace CSet

variable {A B C : Type u}

/-- The underlying set of a countable nondeterministic value. -/
def carrier (x : CSet A) : Set A := x.1

/-- The carrier is countable. -/
theorem carrier_countable (x : CSet A) : x.carrier.Countable := x.2

instance : Membership A (CSet A) := ⟨fun x a ↦ a ∈ x.carrier⟩

/-- Membership is membership in the carrier. -/
@[simp] theorem mem_carrier {x : CSet A} {a : A} : a ∈ x.carrier ↔ a ∈ x := Iff.rfl

/-- Extensionality. -/
@[ext] theorem ext {x y : CSet A} (h : ∀ a, a ∈ x ↔ a ∈ y) : x = y :=
  Subtype.ext (Set.ext h)

/-- Carriers determine values. -/
theorem carrier_injective : Function.Injective (carrier : CSet A → Set A) :=
  fun _ _ h ↦ Subtype.ext h

instance : Monad CSet where
  pure a := ⟨{a}, Set.countable_singleton a⟩
  bind x f := ⟨⋃ a ∈ x.carrier, (f a).carrier, x.2.biUnion fun a _ ↦ (f a).2⟩

/-- Membership in a `pure`. -/
@[simp] theorem mem_pure {a b : A} : b ∈ (pure a : CSet A) ↔ b = a := Iff.rfl

/-- Membership in a bind. -/
@[simp] theorem mem_bind {x : CSet A} {f : A → CSet B} {b : B} :
    b ∈ (x >>= f) ↔ ∃ a, a ∈ x ∧ b ∈ f a := by
  change b ∈ (⋃ a ∈ x.carrier, (f a).carrier) ↔ _
  simp

/-- **Countable nondeterminism is a lawful monad.** -/
instance : LawfulMonad CSet := LawfulMonad.mk'
  (id_map := by
    intro A x
    ext a
    change a ∈ (⋃ b ∈ x.carrier, ({b} : Set A)) ↔ a ∈ x
    simp)
  (pure_bind := by intro A B a f; ext b; simp)
  (bind_assoc := by
    intro A B C x f g
    ext c
    simp only [mem_bind]
    constructor
    · rintro ⟨b, ⟨a, ha, hb⟩, hc⟩; exact ⟨a, ha, b, hb, hc⟩
    · rintro ⟨a, ha, b, hb, hc⟩; exact ⟨b, ⟨a, ha, hb⟩, hc⟩)

/-- Iteration on countable nondeterminism: reachability, which stays countable. -/
instance instIterate : Iterate.{u} CSet where
  iter f a := ⟨{b | Runs (fun a ↦ (f a).carrier) a b},
    runs_countable (fun a ↦ (f a).carrier_countable) a⟩

/-- `iter` on `CSet` is reachability, by definition. -/
@[simp] theorem mem_iter_iff (f : A → CSet (B ⊕ A)) (a : A) (b : B) :
    b ∈ iter f a ↔ Runs (fun a ↦ (f a).carrier) a b := Iff.rfl

/-! ### Transfer of the Elgot laws along the carrier map -/

section Transfer

attribute [local instance] Set.monad

/-- A Kleisli arrow of `CSet`, read as a Kleisli arrow of `Set`. -/
def toSet (f : A → CSet B) : A → Set B := fun a ↦ (f a).carrier

@[simp] theorem toSet_apply (f : A → CSet B) (a : A) : toSet f a = (f a).carrier := rfl

/-- `carrier` preserves `pure`. -/
@[simp] theorem toSet_pure : toSet (pure : A → CSet A) = (pure : A → Set A) := rfl

/-- `carrier` preserves bind, hence Kleisli composition. -/
@[simp] theorem toSet_kcomp (f : A → CSet B) (g : B → CSet C) :
    toSet (kcomp f g) = kcomp (toSet f) (toSet g) := rfl

/-- `carrier` preserves pure Kleisli arrows. -/
@[simp] theorem toSet_liftPure (h : A → B) :
    toSet (liftPure h : A → CSet B) = (liftPure h : A → Set B) := rfl

/-- `carrier` preserves iteration, by construction. -/
@[simp] theorem toSet_iter (f : A → CSet (B ⊕ A)) : toSet (iter f) = iter (toSet f) := rfl

/-- `carrier` commutes with case analysis on a sum. -/
@[simp] theorem toSet_elim {D : Type u} (g : B → CSet D) (h : C → CSet D) :
    toSet (Sum.elim g h) = Sum.elim (toSet g) (toSet h) := by
  funext s; cases s <;> rfl

/-- `carrier` preserves `mapReturn`. -/
@[simp] theorem toSet_mapReturn (f : A → CSet (B ⊕ A)) (g : B → CSet C) :
    toSet (mapReturn f g) = mapReturn (toSet f) (toSet g) := by
  funext a
  change toSet f a >>= toSet (Sum.elim _ _) = toSet f a >>= _
  rw [toSet_elim]
  rfl

/-- `carrier` preserves `flattenBody`. -/
@[simp] theorem toSet_flattenBody (f : A → CSet ((B ⊕ A) ⊕ A)) :
    toSet (flattenBody f) = flattenBody (toSet f) := rfl

/-- Unrolling the loop once. -/
theorem fixpoint (f : A → CSet (B ⊕ A)) :
    iter f = fun a ↦ f a >>= Sum.elim pure (iter f) := by
  funext a
  apply carrier_injective
  change toSet (iter f) a = toSet (fun a ↦ f a >>= Sum.elim pure (iter f)) a
  have h : toSet (fun a ↦ f a >>= Sum.elim pure (iter f))
      = fun a ↦ toSet f a >>= Sum.elim pure (iter (toSet f)) := by
    funext a'
    change toSet f a' >>= toSet (Sum.elim _ _) = _
    rw [toSet_elim, toSet_pure, toSet_iter]
  rw [h, toSet_iter]
  exact congrFun (Nondet.fixpoint (toSet f)) a

/-- Postcomposition commutes with iteration. -/
theorem naturality (f : A → CSet (B ⊕ A)) (g : B → CSet C) :
    kcomp (iter f) g = iter (mapReturn f g) := by
  funext a
  apply carrier_injective
  change toSet (kcomp (iter f) g) a = toSet (iter (mapReturn f g)) a
  rw [toSet_kcomp, toSet_iter, toSet_iter, toSet_mapReturn]
  exact congrFun (Nondet.naturality (toSet f) (toSet g)) a

/-- Iterating an iteration is iterating the flattened body. -/
theorem codiagonal (f : A → CSet ((B ⊕ A) ⊕ A)) :
    iter (iter f) = iter (flattenBody f) := by
  funext a
  apply carrier_injective
  change toSet (iter (iter f)) a = toSet (iter (flattenBody f)) a
  rw [toSet_iter, toSet_iter, toSet_iter, toSet_flattenBody]
  exact congrFun (Nondet.codiagonal (toSet f)) a

/-- Iteration is uniform along pure maps. -/
theorem uniformity (f : A → CSet (B ⊕ A)) (g : C → CSet (B ⊕ C)) (h : A → C)
    (comm : kcomp f (liftPure (Sum.map id h)) = kcomp (liftPure h) g) :
    iter f = kcomp (liftPure h) (iter g) := by
  have square : kcomp (toSet f) (liftPure (Sum.map id h))
      = kcomp (liftPure h) (toSet g) := by
    have := congrArg toSet comm
    rwa [toSet_kcomp, toSet_kcomp, toSet_liftPure, toSet_liftPure] at this
  funext a
  apply carrier_injective
  change toSet (iter f) a = toSet (kcomp (liftPure h) (iter g)) a
  rw [toSet_iter, toSet_kcomp, toSet_liftPure, toSet_iter]
  exact congrFun (Nondet.uniformity (toSet f) (toSet g) h square) a

/-- **Countable nondeterminism is a complete Elgot monad.** -/
instance instLawfulElgotMonad : LawfulElgotMonad.{u} CSet where
  fixpoint := fixpoint
  naturality := naturality
  codiagonal := codiagonal
  uniformity := uniformity

end Transfer

end CSet

end Isotope.Elgot.Nondet
