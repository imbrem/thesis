import Isotope.Elgot.Basic

/-!
# Interaction trees as coherent finite observations

Lean has no primitive coinductive types.  We therefore present an interaction
tree by all of its finite observations, together with the proof that adjacent
observations agree.  Between two visible nodes observation is partial: `none`
is silent divergence, while `some` exposes either a return or a visible event.

This is the weak (tau-insensitive) model of interaction trees.  Consequently
`tau t = t`; finite silent delays are unobservable, whereas an infinite silent
computation is `diverge`.  This equality is the one appropriate for the
complete-Elgot equations, which do not hold for raw, strongly bisimilar ITrees.
-/

namespace Isotope.Elgot.ITree

universe u

/-- One visible observation of an interaction tree. -/
inductive Visible (E : Type u → Type u) (A X : Type (u + 1)) : Type (u + 1)
  | ret (value : A)
  | vis {R : Type u} (event : E R) (next : R → X)

namespace Visible

def map {E : Type u → Type u} {A X Y : Type (u + 1)} (f : X → Y) :
    Visible E A X → Visible E A Y
  | .ret a => .ret a
  | .vis e k => .vis e (f ∘ k)

@[simp] theorem map_ret {E : Type u → Type u} {A X Y : Type (u + 1)} (f : X → Y) (a : A) :
    map f (.ret a : Visible E A X) = .ret a := rfl

@[simp] theorem map_vis {E : Type u → Type u} {A X Y : Type (u + 1)} {R : Type u}
    (f : X → Y) (e : E R) (k : R → X) :
    map f (.vis e k : Visible E A X) = .vis e (f ∘ k) := rfl

theorem map_id {E : Type u → Type u} {A X : Type (u + 1)} (x : Visible E A X) :
    map id x = x := by
  cases x <;> simp [map, Function.comp_def]

theorem map_comp {E : Type u → Type u} {A X Y Z : Type (u + 1)}
    (f : X → Y) (g : Y → Z) (x : Visible E A X) :
    map g (map f x) = map (g ∘ f) x := by
  cases x with
  | ret => rfl
  | vis e k => rfl

end Visible

/-- The observation of a tree to depth `n`.  Depth zero contains no data. -/
def Approx (E : Type u → Type u) (A : Type (u + 1)) : Nat → Type (u + 1)
  | 0 => PUnit
  | n + 1 => Part (Visible E A (Approx E A n))

/-- Forget the deepest visible layer of a finite observation. -/
def Approx.truncate {E : Type u → Type u} {A : Type (u + 1)} :
    (n : Nat) → Approx E A (n + 1) → Approx E A n
  | 0, _ => PUnit.unit
  | n + 1, x => Visible.map (Approx.truncate n) <$> x

/-- A weak interaction tree is a coherent family of finite observations. -/
structure Tree (E : Type u → Type u) (A : Type (u + 1)) : Type (u + 1) where
  observe : (n : Nat) → Approx E A n
  coherent : ∀ n, Approx.truncate n (observe (n + 1)) = observe n

@[ext]
theorem Tree.ext {E : Type u → Type u} {A : Type (u + 1)} {x y : Tree E A}
    (h : ∀ n, x.observe n = y.observe n) : x = y := by
  cases x with
  | mk xo xc =>
    cases y with
    | mk yo yc =>
      simp only [Tree.mk.injEq]
      funext n
      exact h n

/-- Equality of weak ITrees is exactly equality of every finite observation.
This is the public extensional-equality API; no Tau-counting intensional
equality is exposed. -/
theorem Tree.eq_iff_observe {E : Type u → Type u} {A : Type (u + 1)}
    {x y : Tree E A} : x = y ↔ ∀ n, x.observe n = y.observe n := by
  constructor
  · rintro rfl n
    rfl
  · exact Tree.ext

private theorem part_map_eq_some_iff {A B : Type (u + 1)} (f : A → B) (x : Part A) (b : B) :
    b ∈ f <$> x ↔ ∃ a, a ∈ x ∧ f a = b := by
  rw [Part.map_eq_map, Part.mem_map_iff]

private theorem part_map_comp {A B C : Type (u + 1)} (f : A → B) (g : B → C) (x : Part A) :
    g <$> (f <$> x) = (g ∘ f) <$> x := by
  simp only [Part.map_eq_map, Part.map_map]

/-- Return immediately. -/
def ret {E : Type u → Type u} {A : Type (u + 1)} (a : A) : Tree E A where
  observe
    | 0 => PUnit.unit
    | _ + 1 => Part.some (.ret a)
  coherent
    | 0 => rfl
    | _ + 1 => by simp [Approx.truncate]

/-- Silent divergence: no finite visible observation is ever produced. -/
def diverge {E : Type u → Type u} {A : Type (u + 1)} : Tree E A where
  observe
    | 0 => PUnit.unit
    | _ + 1 => Part.none
  coherent
    | 0 => rfl
    | _ + 1 => by simp [Approx.truncate]

/-- Perform one visible event and continue from its response. -/
def vis {E : Type u → Type u} {A : Type (u + 1)} {R : Type u}
    (e : E R) (k : R → Tree E A) : Tree E A where
  observe
    | 0 => PUnit.unit
    | n + 1 => Part.some (.vis e (fun r => (k r).observe n))
  coherent
    | 0 => rfl
    | n + 1 => by
      simp only [Approx.truncate, Part.map_eq_map, Part.map_some, Visible.map_vis]
      congr
      funext r
      exact (k r).coherent n

/-- A finite silent step is observationally irrelevant in the weak model. -/
def tau {E : Type u → Type u} {A : Type (u + 1)} (t : Tree E A) : Tree E A := t

@[simp] theorem tau_eq {E : Type u → Type u} {A : Type (u + 1)} (t : Tree E A) : tau t = t := rfl

end Isotope.Elgot.ITree
