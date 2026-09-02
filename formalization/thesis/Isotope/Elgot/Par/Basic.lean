import Isotope.Elgot.Basic
import Mathlib.Order.Basic

/-!
# A uniform interface for parallel composition

Four parallel-composition operators occur in this development, over four different notions of
computation:

| operator | file | shape |
|---|---|---|
| Brookes interleaving | `Isotope/Elgot/Brookes/TSO/Interleaving.lean` | `M A → M B → M (A×B)` |
| store-buffer TSO | the same operator at `c = SeqCst.rewriting (St …)` | `M A → M B → M (A×B)` |
| release/acquire `∥∥∥` | `Isotope/Elgot/RA/Parallel.lean` | `M A → M B → M (A × B)` |
| pomset `∥` | `Isotope/Pomset/Quotient.lean` | `P → P → P` |

The first three share the *typed* shape `M A → M B → M (A × B)`: parallel composition is a
second, concurrent tensor on the computation monad, in the sense of Dvir–Kammar–Lahav
(TOPLAS 47(2):7, §7.1 p.27), and is deliberately **not** a monad operation.  The pomset
operator is homogeneous, has no monad under it, and satisfies its laws *on the nose* rather
than up to a coherence isomorphism.

This module gives one class per law rather than a single bundled "symmetric monoidal monad"
class, because **no operator here satisfies all of them**: release/acquire `∥∥∥` has no
associativity proof (and, since `inf_μ` is characterised rather than constructed, no
prospect of one in the present design — see the honest boundary of `Isotope/Elgot/RA.lean`),
while the pomset operator has no `bind` to interchange with.  Splitting the laws is what
makes the partial instances expressible.  `Isotope/Elgot/Par/Summary.lean` records which
model satisfies which.

## The bridge between the two shapes

`ParMonoid` axiomatises the homogeneous shape.  `Par.punitParMonoid` derives one from the
typed shape at the type `M PUnit` of *unit-returning* computations, so the pomset operator
and the interleaving operators become comparable: both are commutative monoids on the
computations that return nothing.
-/

universe u

namespace Isotope.Elgot.Par

/-! ## The typed shape -/

/-- A parallel-composition operator on a notion of computation: a second, *concurrent*
tensor `M A → M B → M (A × B)`, not a monad operation. -/
class ParOp (M : Type u → Type u) where
  /-- Run both computations concurrently and return both results. -/
  par : {A B : Type u} → M A → M B → M (A × B)

export ParOp (par)

/-- The associator `(A × B) × C → A × (B × C)`. -/
def assocRL {A B C : Type u} (p : (A × B) × C) : A × B × C := (p.1.1, p.1.2, p.2)

/-- The inverse associator `A × (B × C) → (A × B) × C`. -/
def assocLR {A B C : Type u} (p : A × B × C) : (A × B) × C := ((p.1, p.2.1), p.2.2)

@[simp] theorem assocRL_assocLR {A B C : Type u} (p : A × B × C) :
    assocRL (assocLR p) = p := rfl

@[simp] theorem assocLR_assocRL {A B C : Type u} (p : (A × B) × C) :
    assocLR (assocRL p) = p := rfl

/-- Parallel composition is monotone in both arguments: the refinement half of
Dvir–Kammar–Lahav's Proposition 7.4 and of the corresponding Brookes fact. -/
class ParMono (M : Type u → Type u) [ParOp M] [∀ A, Preorder (M A)] : Prop where
  /-- Monotonicity in both arguments. -/
  par_mono {A B : Type u} {x x' : M A} {y y' : M B} : x ≤ x' → y ≤ y' → par x y ≤ par x' y'

/-- Symmetry: swapping the two threads swaps the two results, on the nose. -/
class ParSymm (M : Type u → Type u) [Monad M] [ParOp M] : Prop where
  /-- `x ∥ y` is `y ∥ x` with the returned pair swapped. -/
  par_swap {A B : Type u} (x : M A) (y : M B) : Prod.swap <$> par x y = par y x

/-- Associativity, up to the associator. -/
class ParAssoc (M : Type u → Type u) [Monad M] [ParOp M] : Prop where
  /-- `(x ∥ y) ∥ z = x ∥ (y ∥ z)`, up to reassociating the returned triple. -/
  par_assoc {A B C : Type u} (x : M A) (y : M B) (z : M C) :
    assocRL <$> par (par x y) z = par x (par y z)

/-- The unit laws: `pure ()` is a unit for parallel composition. -/
class ParUnit (M : Type u → Type u) [Monad M] [ParOp M] : Prop where
  /-- The idle thread on the right is a unit. -/
  par_unit_right {A : Type u} (x : M A) :
    (Prod.fst : A × PUnit.{u + 1} → A) <$> par x (pure PUnit.unit) = x
  /-- The idle thread on the left is a unit. -/
  par_unit_left {A : Type u} (x : M A) :
    (Prod.snd : PUnit.{u + 1} × A → A) <$> par (pure PUnit.unit) x = x

/-- Naturality: relabelling the result of one thread relabels the corresponding component of
the pair.  This is what makes parallel composition a *bifunctor* on the Kleisli category's
pure part. -/
class ParNat (M : Type u → Type u) [Monad M] [ParOp M] : Prop where
  /-- Naturality in the left argument. -/
  par_map_left {A A' B : Type u} (f : A → A') (x : M A) (y : M B) :
    par (f <$> x) y = Prod.map f id <$> par x y
  /-- Naturality in the right argument. -/
  par_map_right {A B B' : Type u} (g : B → B') (x : M A) (y : M B) :
    par x (g <$> y) = Prod.map id g <$> par x y

/-- The interchange law between the concurrent and the sequential tensor: running the two
threads in lockstep is *at most* running them concurrently.  It is an inequality, not an
equality: the interleavings of `x ; f` with `y ; g` include ones that cross the seam. -/
class ParExchange (M : Type u → Type u) [Monad M] [ParOp M] [∀ A, Preorder (M A)] : Prop where
  /-- `(x ∥ y) ; (f ∥ g) ≤ (x ; f) ∥ (y ; g)`. -/
  exchange {A A' B B' : Type u} (x : M A) (y : M B) (f : A → M A') (g : B → M B') :
    (par x y >>= fun p ↦ par (f p.1) (g p.2)) ≤ par (x >>= f) (y >>= g)

/-- Thread inlining: running the two threads one after the other is one of the ways of
running them concurrently.  This is the `M ∥ N ↠ ⟨M, N⟩` of Dvir–Kammar–Lahav's Fig. 3
(journal p.12), read in the direction the refinement order goes here. -/
class ParInline (M : Type u → Type u) [Monad M] [ParOp M] [∀ A, Preorder (M A)] : Prop where
  /-- Sequencing refines parallel composition. -/
  inline_le_par {A B : Type u} (x : M A) (y : M B) :
    (x >>= fun a ↦ y >>= fun b ↦ pure (a, b)) ≤ par x y

/-! ## The homogeneous shape -/

/-- A commutative monoid of parallel composition on a single type, with no monad underneath:
the shape the pomset operator `Isotope.Pomset.Pom.par` has.  Kept separate from Mathlib's
`CommMonoid` because a type may already carry a *sequential* monoid structure — as `Pom A`
does — and only one `Monoid` instance is available per type. -/
class ParMonoid (P : Type u) where
  /-- Parallel composition. -/
  par : P → P → P
  /-- The idle computation. -/
  unit : P
  /-- Parallel composition is associative. -/
  par_assoc (x y z : P) : par (par x y) z = par x (par y z)
  /-- Parallel composition is commutative. -/
  par_comm (x y : P) : par x y = par y x
  /-- The idle computation is a unit. -/
  par_unit (x : P) : par x unit = x

namespace ParMonoid

variable {P : Type u} [ParMonoid P]

/-- The idle computation is a unit on the left too. -/
theorem unit_par (x : P) : par unit x = x := by rw [par_comm, par_unit]

end ParMonoid

/-! ## The bridge

Any typed parallel composition satisfying symmetry, associativity, the unit law and
naturality restricts to a commutative monoid on unit-returning computations.  This is what
lets the pomset operator and the interleaving operators be compared at all: they live in
different worlds, but both are `ParMonoid`s. -/

/-- Parallel composition of unit-returning computations, with the trivial return value
discarded. -/
def parU {M : Type u → Type u} [Monad M] [ParOp M]
    (x y : M PUnit.{u + 1}) : M PUnit.{u + 1} :=
  (fun _ ↦ PUnit.unit) <$> par x y

/-- Any two functions into `PUnit` are equal. -/
theorem funext_punit {α : Type u} (f g : α → PUnit) : f = g := by
  funext a; exact rfl

/-- **The bridge.**  A typed parallel composition with symmetry, associativity, unit and
naturality is a commutative monoid on unit-returning computations. -/
@[reducible] def punitParMonoid (M : Type u → Type u) [Monad M] [LawfulMonad M] [ParOp M]
    [ParSymm M] [ParAssoc M] [ParUnit M] [ParNat M] : ParMonoid (M PUnit.{u + 1}) where
  par := parU
  unit := pure PUnit.unit
  par_comm x y := by
    change (fun _ ↦ PUnit.unit) <$> par x y = (fun _ ↦ PUnit.unit) <$> par y x
    rw [← ParSymm.par_swap x y, ← comp_map]
  par_assoc x y z := by
    change (fun _ ↦ PUnit.unit) <$> par ((fun _ ↦ PUnit.unit) <$> par x y) z
      = (fun _ ↦ PUnit.unit) <$> par x ((fun _ ↦ PUnit.unit) <$> par y z)
    rw [ParNat.par_map_left, ParNat.par_map_right, ← comp_map, ← comp_map,
      ← ParAssoc.par_assoc x y z, ← comp_map]
    rfl
  par_unit x := by
    change (fun _ ↦ PUnit.unit) <$> par x (pure PUnit.unit : M PUnit.{u + 1}) = x
    rw [funext_punit (fun _ : PUnit.{u + 1} × PUnit.{u + 1} ↦ PUnit.unit)
      (Prod.fst : PUnit.{u + 1} × PUnit.{u + 1} → PUnit.{u + 1}), ParUnit.par_unit_right]

end Isotope.Elgot.Par
