import Isotope.Elgot.Morphism
import Isotope.Elgot.Nondet

/-!
# Concrete Elgot morphisms between the nondeterminism monads

The three set-flavoured monads of `Isotope/Elgot/` sit in a chain

```
Part  ↪  CSet  ↪  SetM
```

sending a computation to the set of values it may produce.  Every map in the
chain preserves `pure`, `>>=` **and** `iter`, so each is an `ElgotHom`, and the
triangle commutes on the nose.

## Why `iter` is preserved

All three monads iterate by *reachability*: `b ∈ iter f a` iff some finite
unfolding of `f` starting at `a` returns `b`.  `Part.Runs` and
`Nondet.Runs` are literally the same inductive definition read in two
different powersets, and `CSet`'s iteration is `Set`'s carried along the
subtype.  The interesting content is therefore concentrated in one lemma,
`Part.runs_iff_setRuns`.

This is also the precise sense in which the chain *loses* information: `Part`
distinguishes divergence from failure only in that a divergent loop has an
empty graph, and so does a failing one — the `Set` reading identifies them.
`Part.toSet` is nonetheless injective (`Part.toSet_injective`), so the first
map is an embedding; it is not surjective, since a two-element set is not the
graph of a partial value.
-/

namespace Isotope.Elgot

open Isotope.Elgot.Nondet

universe u

variable {A B C : Type u}

section

attribute [local instance] Set.monad

/-! ### `Part → SetM`: the graph of a partial value -/

namespace Part

/-- The graph of a partial value: the set of values it may return, which is a
subsingleton. -/
def toSet (x : _root_.Part A) : Set A := {a | a ∈ x}

@[simp] theorem mem_toSet {x : _root_.Part A} {a : A} : a ∈ toSet x ↔ a ∈ x := Iff.rfl

/-- The graph of a partial value has at most one element. -/
theorem toSet_subsingleton (x : _root_.Part A) : (toSet x).Subsingleton :=
  fun _ ha _ hb => _root_.Part.mem_unique ha hb

/-- Distinct partial values have distinct graphs. -/
theorem toSet_injective : Function.Injective (toSet (A := A)) := fun x y h =>
  _root_.Part.ext fun a => by
    have := congrArg (fun s => a ∈ s) h
    simpa [toSet] using this

/-- The graph of a returned value is a singleton. -/
@[simp] theorem toSet_pure (a : A) : toSet (pure a : _root_.Part A) = pure a := by
  apply Set.ext
  intro b
  simp [toSet, _root_.Part.mem_some_iff]

/-- The graph of a sequenced computation is the sequenced graph. -/
@[simp] theorem toSet_bind (x : _root_.Part A) (f : A → _root_.Part B) :
    toSet (x >>= f) = (toSet x >>= fun a => toSet (f a)) := by
  apply Set.ext
  intro b
  rw [mem_bind_iff]
  simp only [mem_toSet, _root_.Part.bind_eq_bind, _root_.Part.mem_bind_iff]

/-- A successful run of a partial loop body is a successful run of its graph,
and conversely.  The two `Runs` predicates are the same definition. -/
theorem runs_iff_setRuns (f : A → _root_.Part (B ⊕ A)) (a : A) (b : B) :
    Part.Runs f a b ↔ Nondet.Runs (fun a => toSet (f a)) a b := by
  constructor
  · intro h
    induction h with
    | done hs => exact .done hs
    | more hs _ ih => exact .more hs ih
  · intro h
    induction h with
    | done hs => exact .done hs
    | more hs _ ih => exact .more hs ih

/-- The graph of an iteration is the iteration of the graph. -/
@[simp] theorem toSet_iter (f : A → _root_.Part (B ⊕ A)) (a : A) :
    toSet (iter f a) = iter (fun a => toSet (f a)) a := by
  apply Set.ext
  intro b
  rw [mem_toSet, Part.mem_iter_iff, Nondet.mem_iter_iff]
  exact runs_iff_setRuns f a b

/-- **The graph map is an Elgot monad morphism `Part → SetM`.**  This is the
"a partial function is a nondeterministic one that happens to be
deterministic" comparison. -/
noncomputable def toSetHom : ElgotHom.{u} _root_.Part SetM where
  app x := toSet x
  app_pure a := toSet_pure a
  app_bind x f := toSet_bind x f
  app_iter f a := toSet_iter f a

@[simp] theorem toSetHom_app (x : _root_.Part A) : toSetHom.app x = toSet x := rfl

/-! ### `Part → CSet`: the same map, landing in countable sets -/

/-- The graph of a partial value as a *countable* set: a subsingleton is
countable. -/
def toCSet (x : _root_.Part A) : CSet A := ⟨toSet x, (toSet_subsingleton x).countable⟩

@[simp] theorem mem_toCSet {x : _root_.Part A} {a : A} : a ∈ toCSet x ↔ a ∈ x := Iff.rfl

@[simp] theorem carrier_toCSet (x : _root_.Part A) : (toCSet x).carrier = toSet x := rfl

/-- **The graph map is an Elgot monad morphism `Part → CSet`.** -/
noncomputable def toCSetHom : ElgotHom.{u} _root_.Part CSet where
  app x := toCSet x
  app_pure a := by ext b; simp [_root_.Part.mem_some_iff]
  app_bind x f := by
    ext b
    simp only [mem_toCSet, _root_.Part.bind_eq_bind, _root_.Part.mem_bind_iff,
      CSet.mem_bind, mem_toCSet]
  app_iter f a := by
    ext b
    rw [mem_toCSet, Part.mem_iter_iff, CSet.mem_iter_iff]
    exact runs_iff_setRuns f a b

@[simp] theorem toCSetHom_app (x : _root_.Part A) : toCSetHom.app x = toCSet x := rfl

end Part

/-! ### `CSet → SetM`: forget countability -/

namespace Nondet.CSet

/-- **Forgetting countability is an Elgot monad morphism `CSet → SetM`.**
Every law holds because `CSet`'s operations are defined as `Set`'s carried
along the subtype; `iter` in particular is preserved *definitionally*. -/
def toSetHom : ElgotHom.{u} CSet SetM where
  app x := x.carrier
  app_pure a := rfl
  app_bind x f := by
    show ((x >>= f).carrier : Set _) = (x.carrier >>= fun a => (f a).carrier)
    apply Set.ext
    intro b
    rw [mem_bind_iff]
    simp only [CSet.mem_carrier, CSet.mem_bind]
  app_iter f a := rfl

@[simp] theorem toSetHom_app (x : CSet A) : toSetHom.app x = x.carrier := rfl

end Nondet.CSet

/-- **The comparison triangle commutes**: taking the graph of a partial value
and forgetting countability is taking the graph. -/
theorem Part.toCSetHom_comp_toSetHom :
    Part.toCSetHom.{u}.comp Nondet.CSet.toSetHom = Part.toSetHom :=
  ElgotHom.ext fun _ => rfl

end

end Isotope.Elgot
