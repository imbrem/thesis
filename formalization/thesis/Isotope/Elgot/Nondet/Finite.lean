import Isotope.Elgot.Basic
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Finset.Functor
import Mathlib.Data.ULift
import Mathlib.Logic.Equiv.Defs

/-!
# Finite nondeterminism is not an Elgot monad

The finite-powerset monad is a perfectly good lawful monad, but it admits **no** iteration
operator satisfying even the Elgot fixpoint law — indeed none satisfying the fixpoint *inclusion*.
The obstruction is that the reflexive-transitive closure of a finitely-branching relation need not
be finitely branching: the body

    n ↦ {inl n, inr (n + 1)}

branches twice but reaches every natural number.

Note that `¬ Nonempty (Iterate FinSet)` is *false* (`nonempty_iterate` below): `Iterate` carries no
equations, so `fun _ _ ↦ ∅` is a witness.  The impossibility is necessarily relative to the laws.
-/

namespace Isotope.Elgot.Nondet

universe u

/-! ### The carrier-independent kernel

Everything about finite nondeterminism that the argument uses is packaged as hypotheses: a monad
with powerset-style membership whose extents at one infinite type are finite.
-/

/-- **No monad with finite powerset-style extents admits a lax iteration operator.**

`mem` is an abstract membership predicate on `m`, `e : ℕ → N` codes the state space, and `body`
is the two-way-branching ray.  Only the *inclusion* half of the fixpoint law is assumed, so this
refutes lax (post-)fixpoints as well as genuine fixpoints. -/
theorem no_finite_lax_iteration {m : Type u → Type u} [Monad m] {N : Type u}
    (mem : {A : Type u} → A → m A → Prop)
    (mem_pure : ∀ {A : Type u} (a b : A), mem b (pure a) ↔ b = a)
    (mem_bind : ∀ {A B : Type u} (x : m A) (g : A → m B) (b : B),
      mem b (x >>= g) ↔ ∃ a, mem a x ∧ mem b (g a))
    (e : ℕ → N) (he : Function.Injective e)
    (finite : ∀ x : m N, {k : N | mem k x}.Finite)
    (body : N → m (N ⊕ N))
    (mem_body : ∀ (n : ℕ) (s : N ⊕ N),
      mem s (body (e n)) ↔ s = Sum.inl (e n) ∨ s = Sum.inr (e (n + 1)))
    (it : N → m N)
    (hlax : ∀ n : N, ∀ k : N, mem k (body n >>= Sum.elim pure it) → mem k (it n)) :
    False := by
  -- One unfolding, in membership form, restricted to the ray.
  have hstep : ∀ (n : ℕ) (k : N), (k = e n ∨ mem k (it (e (n + 1)))) → mem k (it (e n)) := by
    intro n k hk
    refine hlax (e n) k ((mem_bind _ _ _).mpr ?_)
    rcases hk with rfl | hk
    · exact ⟨Sum.inl (e n), (mem_body n _).mpr (Or.inl rfl), (mem_pure _ _).mpr rfl⟩
    · exact ⟨Sum.inr (e (n + 1)), (mem_body n _).mpr (Or.inr rfl), hk⟩
  -- Each state returns its own index.
  have hself : ∀ n : ℕ, mem (e n) (it (e n)) := fun n ↦ hstep n (e n) (Or.inl rfl)
  -- Later states contribute to earlier ones.
  have hmono : ∀ (n : ℕ) (k : N), mem k (it (e (n + 1))) → mem k (it (e n)) :=
    fun n k hk ↦ hstep n k (Or.inr hk)
  have hsub : ∀ (n : ℕ) (k : N), mem k (it (e n)) → mem k (it (e 0)) := by
    intro n
    induction n with
    | zero => exact fun _ hk ↦ hk
    | succ n ih => exact fun k hk ↦ ih k (hmono n k hk)
  -- Hence the whole ray is in the extent at the start state.
  have hall : ∀ n : ℕ, e n ∈ {k : N | mem k (it (e 0))} := fun n ↦ hsub n (e n) (hself n)
  exact Set.infinite_of_injective_forall_mem he hall (finite (it (e 0)))

/-- The equational fixpoint law implies its lax form, so the kernel applies to it. -/
theorem no_finite_iteration {m : Type u → Type u} [Monad m] {N : Type u}
    (mem : {A : Type u} → A → m A → Prop)
    (mem_pure : ∀ {A : Type u} (a b : A), mem b (pure a) ↔ b = a)
    (mem_bind : ∀ {A B : Type u} (x : m A) (g : A → m B) (b : B),
      mem b (x >>= g) ↔ ∃ a, mem a x ∧ mem b (g a))
    (e : ℕ → N) (he : Function.Injective e)
    (finite : ∀ x : m N, {k : N | mem k x}.Finite)
    (body : N → m (N ⊕ N))
    (mem_body : ∀ (n : ℕ) (s : N ⊕ N),
      mem s (body (e n)) ↔ s = Sum.inl (e n) ∨ s = Sum.inr (e (n + 1)))
    (it : N → m N)
    (hfix : ∀ n : N, it n = body n >>= Sum.elim pure it) :
    False :=
  no_finite_lax_iteration mem mem_pure mem_bind e he finite body mem_body it
    (fun n _k hk ↦ (hfix n) ▸ hk)

/-! ### The decidability-free finite powerset -/

/-- Finitely-supported nondeterminism, as an endofunctor of `Type u`.  Unlike `Finset` this needs
no decidable equality, so it is a genuine `Monad (Type u → Type u)`. -/
def FinSet (A : Type u) : Type u := {s : Set A // s.Finite}

namespace FinSet

variable {A B C : Type u}

/-- The underlying set of a finite nondeterministic value. -/
def carrier (x : FinSet A) : Set A := x.1

/-- The carrier is finite. -/
theorem carrier_finite (x : FinSet A) : x.carrier.Finite := x.2

instance : Membership A (FinSet A) := ⟨fun x a ↦ a ∈ x.carrier⟩


/-- Membership is membership in the carrier. -/
@[simp] theorem mem_carrier {x : FinSet A} {a : A} : a ∈ x.carrier ↔ a ∈ x := Iff.rfl

/-- Extensionality for finite nondeterministic values. -/
@[ext] theorem ext {x y : FinSet A} (h : ∀ a, a ∈ x ↔ a ∈ y) : x = y :=
  Subtype.ext (Set.ext h)

instance : Monad FinSet where
  pure a := ⟨{a}, Set.finite_singleton a⟩
  bind x f := ⟨⋃ a ∈ x.carrier, (f a).carrier, x.2.biUnion fun a _ ↦ (f a).2⟩

/-- Membership in a `pure`. -/
@[simp] theorem mem_pure {a b : A} : b ∈ (pure a : FinSet A) ↔ b = a := Iff.rfl

/-- Membership in a bind. -/
@[simp] theorem mem_bind {x : FinSet A} {f : A → FinSet B} {b : B} :
    b ∈ (x >>= f) ↔ ∃ a, a ∈ x ∧ b ∈ f a := by
  change b ∈ (⋃ a ∈ x.carrier, (f a).carrier) ↔ _
  simp

/-- **Positive companion**: finite nondeterminism *is* a lawful monad; only iteration fails. -/
instance : LawfulMonad FinSet := LawfulMonad.mk'
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

/-- Extents are finite, by construction. -/
theorem finite_setOf_mem (x : FinSet A) : {a : A | a ∈ x}.Finite := x.2

/-- The witness body: from `n`, either return `n` or loop with `n + 1`. -/
def body (n : ULift.{u} ℕ) : FinSet (ULift.{u} ℕ ⊕ ULift.{u} ℕ) :=
  ⟨{Sum.inl n, Sum.inr (ULift.up (n.down + 1))},
    (Set.finite_singleton _).insert _⟩

/-- The witness body branches exactly twice. -/
@[simp] theorem mem_body {n : ULift.{u} ℕ} {s : ULift.{u} ℕ ⊕ ULift.{u} ℕ} :
    s ∈ body n ↔ s = Sum.inl n ∨ s = Sum.inr (ULift.up (n.down + 1)) := Iff.rfl

/-- **No family of finite sets satisfies the fixpoint inclusion for `body`.** -/
theorem no_lax_fixpoint (it : ULift.{u} ℕ → FinSet (ULift.{u} ℕ))
    (hlax : ∀ (n k : ULift.{u} ℕ), k ∈ (body n >>= Sum.elim pure it) → k ∈ it n) : False :=
  no_finite_lax_iteration (m := FinSet.{u}) (fun a x ↦ a ∈ x)
    (fun _ _ ↦ mem_pure) (fun _ _ _ ↦ mem_bind)
    ULift.up ULift.up_injective finite_setOf_mem body (fun _ _ ↦ mem_body) it hlax

/-- No family of finite sets satisfies the fixpoint equation for `body`. -/
theorem no_fixpoint (it : ULift.{u} ℕ → FinSet (ULift.{u} ℕ))
    (hfix : ∀ n, it n = body n >>= Sum.elim pure it) : False :=
  no_lax_fixpoint it (fun n _k hk ↦ (hfix n) ▸ hk)

/-- `Iterate FinSet` *is* inhabited: the class carries no equations.  This is why the
impossibility below is stated relative to the laws. -/
theorem nonempty_iterate : Nonempty (Iterate.{u} FinSet) :=
  ⟨⟨fun _ _ ↦ ⟨∅, Set.finite_empty⟩⟩⟩

/-- **No iteration operator on finite nondeterminism satisfies the Elgot fixpoint law.** -/
theorem not_iterate_fixpoint :
    ¬ ∃ I : Iterate.{u} FinSet,
        ∀ {A B : Type u} (f : A → FinSet (B ⊕ A)),
          I.iter f = fun a ↦ f a >>= Sum.elim pure (I.iter f) := by
  rintro ⟨I, hI⟩
  exact no_fixpoint (I.iter body) (fun n ↦ congrFun (hI body) n)

/-- **Finite nondeterminism is not an Elgot monad.** -/
theorem not_lawfulElgotMonad (I : Iterate.{u} FinSet) :
    ¬ @LawfulElgotMonad FinSet _ _ I := by
  intro h
  exact not_iterate_fixpoint ⟨I, fun f ↦ h.fixpoint f⟩

/-- The same, phrased for `Nonempty`. -/
theorem not_nonempty_lawfulElgotMonad :
    ¬ ∃ I : Iterate.{u} FinSet, Nonempty (@LawfulElgotMonad FinSet _ _ I) := by
  rintro ⟨I, ⟨h⟩⟩
  exact not_lawfulElgotMonad I h

end FinSet

/-! ### The same for Mathlib's `Finset`

Mathlib's `Finset` monad is classical (it needs `[∀ P, Decidable P]`), so the statements are
guarded by `open scoped Classical`.  Repeating the argument here shows that the failure is not an
artifact of the decidability-free presentation.
-/

namespace FinsetCounterexample

open scoped Classical in
/-- Membership in a `Finset` `pure`. -/
theorem mem_pure {A : Type u} (a b : A) : b ∈ (pure a : Finset A) ↔ b = a := by
  simp

open scoped Classical in
/-- Membership in a `Finset` bind. -/
theorem mem_bind {A B : Type u} (x : Finset A) (g : A → Finset B) (b : B) :
    b ∈ (x >>= g) ↔ ∃ a, a ∈ x ∧ b ∈ g a := by
  simp [Finset.mem_sup]

/-- The witness body, as a `Finset`. -/
def body (n : ULift.{u} ℕ) : Finset (ULift.{u} ℕ ⊕ ULift.{u} ℕ) :=
  {Sum.inl n, Sum.inr (ULift.up (n.down + 1))}

/-- The witness body branches exactly twice. -/
@[simp] theorem mem_body {n : ULift.{u} ℕ} {s : ULift.{u} ℕ ⊕ ULift.{u} ℕ} :
    s ∈ body n ↔ s = Sum.inl n ∨ s = Sum.inr (ULift.up (n.down + 1)) := by
  simp [body]

open scoped Classical in
/-- **No family of `Finset`s satisfies the fixpoint inclusion for `body`.** -/
theorem no_lax_fixpoint (it : ULift.{u} ℕ → Finset (ULift.{u} ℕ))
    (hlax : ∀ (n k : ULift.{u} ℕ), k ∈ (body n >>= Sum.elim pure it) → k ∈ it n) : False :=
  no_finite_lax_iteration (m := Finset.{u}) (fun a x ↦ a ∈ x)
    mem_pure mem_bind ULift.up ULift.up_injective
    (fun x ↦ x.finite_toSet) body (fun _ _ ↦ mem_body) it hlax

open scoped Classical in
/-- **No iteration operator on `Finset` satisfies the Elgot fixpoint law.** -/
theorem not_iterate_fixpoint :
    ¬ ∃ I : Iterate.{u} Finset,
        ∀ {A B : Type u} (f : A → Finset (B ⊕ A)),
          I.iter f = fun a ↦ f a >>= Sum.elim pure (I.iter f) := by
  rintro ⟨I, hI⟩
  exact no_lax_fixpoint (I.iter body) (fun n k hk ↦ (congrFun (hI body) n) ▸ hk)

open scoped Classical in
/-- **Mathlib's finite-powerset monad is not an Elgot monad.** -/
theorem not_lawfulElgotMonad (I : Iterate.{u} Finset) :
    ¬ @LawfulElgotMonad Finset _ _ I := by
  intro h
  exact not_iterate_fixpoint ⟨I, fun f ↦ h.fixpoint f⟩

end FinsetCounterexample

end Isotope.Elgot.Nondet
