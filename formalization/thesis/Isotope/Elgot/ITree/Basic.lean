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

/-- Relabel the children of one visible observation. -/
def map {E : Type u → Type u} {A X Y : Type (u + 1)} (f : X → Y) :
    Visible E A X → Visible E A Y
  | .ret a => .ret a
  | .vis e k => .vis e (f ∘ k)

/-- `Visible.map` on a return. -/
@[simp] theorem map_ret {E : Type u → Type u} {A X Y : Type (u + 1)} (f : X → Y) (a : A) :
    map f (.ret a : Visible E A X) = .ret a := rfl

/-- `Visible.map` on a visible event. -/
@[simp] theorem map_vis {E : Type u → Type u} {A X Y : Type (u + 1)} {R : Type u}
    (f : X → Y) (e : E R) (k : R → X) :
    map f (.vis e k : Visible E A X) = .vis e (f ∘ k) := rfl

/-- `Visible.map` preserves identities. -/
theorem map_id {E : Type u → Type u} {A X : Type (u + 1)} (x : Visible E A X) :
    map id x = x := by
  cases x <;> simp [map, Function.comp_def]

/-- `Visible.map` preserves composition. -/
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

/-- Trees agreeing at every observation depth are equal. -/
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

/-- Depth-zero observations carry no information. -/
theorem Approx.eq_zero {E : Type u → Type u} {A : Type (u + 1)} (x y : Approx E A 0) :
    x = y := rfl

/-- The observations of `ret`. -/
theorem observe_ret {E : Type u → Type u} {A : Type (u + 1)} (a : A) (n : Nat) :
    (ret (E := E) a).observe (n + 1) = Part.some (.ret a) := rfl

/-- The observations of `diverge`: never a visible head. -/
theorem observe_diverge {E : Type u → Type u} {A : Type (u + 1)} (n : Nat) :
    (diverge (E := E) (A := A)).observe (n + 1) = Part.none := rfl

/-- The observations of `vis`. -/
theorem observe_vis {E : Type u → Type u} {A : Type (u + 1)} {R : Type u}
    (e : E R) (k : R → Tree E A) (n : Nat) :
    (vis e k).observe (n + 1) = Part.some (.vis e (fun r => (k r).observe n)) := rfl

/-- A returned value is distinguishable from silent divergence. -/
theorem ret_ne_diverge {E : Type u → Type u} {A : Type (u + 1)} (a : A) :
    (ret (E := E) a) ≠ diverge := by
  intro h
  have := congrFun (congrArg Tree.observe h) 1
  rw [observe_ret, observe_diverge] at this
  exact (Part.notMem_none (Visible.ret a : Visible E A (Approx E A 0)))
    (this ▸ Part.mem_some (Visible.ret a : Visible E A (Approx E A 0)))

/-- A visible event is distinguishable from silent divergence. -/
theorem vis_ne_diverge {E : Type u → Type u} {A : Type (u + 1)} {R : Type u}
    (e : E R) (k : R → Tree E A) : vis e k ≠ diverge := by
  intro h
  have := congrFun (congrArg Tree.observe h) 1
  rw [observe_vis, observe_diverge] at this
  exact (Part.notMem_none _) (this ▸ Part.mem_some _)

/-- A returned value is distinguishable from a visible event. -/
theorem ret_ne_vis {E : Type u → Type u} {A : Type (u + 1)} {R : Type u}
    (a : A) (e : E R) (k : R → Tree E A) : ret a ≠ vis e k := by
  intro h
  have := congrFun (congrArg Tree.observe h) 1
  rw [observe_ret, observe_vis] at this
  have h2 : (Part.some (Visible.ret a) : Part (Visible E A (Approx E A 0))) =
      Part.some (Visible.vis e (fun r => (k r).observe 0)) := this
  simp only [Part.some_inj] at h2
  cases h2

/-- Unfold a `Part ∘ Visible`-coalgebra into finite observations. -/
def Approx.corec {E : Type u → Type u} {A X : Type (u + 1)}
    (h : X → Part (Visible E A X)) : (n : Nat) → X → Approx E A n
  | 0, _ => PUnit.unit
  | n + 1, x => Visible.map (Approx.corec h n) <$> h x

/-- Unfolding a coalgebra produces a coherent family of observations. -/
theorem Approx.truncate_corec {E : Type u → Type u} {A X : Type (u + 1)}
    (h : X → Part (Visible E A X)) (n : Nat) (x : X) :
    truncate n (corec h (n + 1) x) = corec h n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [truncate, corec, Part.map_eq_map, Part.map_map]
      congr 1
      funext node
      rw [Function.comp_apply, Visible.map_comp]
      congr 1
      funext y
      exact ih y

/-- Guarded corecursion: the unique tree unfolding a `Part ∘ Visible`-coalgebra. -/
def corec {E : Type u → Type u} {A X : Type (u + 1)}
    (h : X → Part (Visible E A X)) (x : X) : Tree E A where
  observe n := Approx.corec h n x
  coherent n := Approx.truncate_corec h n x

/-- One guarded unfolding step of `corec`. -/
theorem observe_corec {E : Type u → Type u} {A X : Type (u + 1)}
    (h : X → Part (Visible E A X)) (x : X) (n : Nat) :
    (corec h x).observe (n + 1) =
      Visible.map (fun y => (corec h y).observe n) <$> h x := rfl

/-- `corec h` is the unique guarded unfolding of `h`; this is the coinduction
principle for the extensional carrier. -/
theorem corec_unique {E : Type u → Type u} {A X : Type (u + 1)}
    (h : X → Part (Visible E A X)) (F : X → Tree E A)
    (hF : ∀ (x : X) (n : Nat),
      (F x).observe (n + 1) = Visible.map (fun y => (F y).observe n) <$> h x) :
    F = corec h := by
  funext x
  apply Tree.ext
  intro n
  induction n generalizing x with
  | zero => exact Approx.eq_zero _ _
  | succ n ih =>
      rw [hF x, observe_corec]
      have hfun : (fun y => (F y).observe n) = (fun y => (corec h y).observe n) :=
        funext (fun y => ih y)
      rw [hfun]

/-- A finite silent step is observationally irrelevant in the weak model. -/
def tau {E : Type u → Type u} {A : Type (u + 1)} (t : Tree E A) : Tree E A := t

/-- `tau` is definitionally the identity: finite silent delays are unobservable. -/
@[simp] theorem tau_eq {E : Type u → Type u} {A : Type (u + 1)} (t : Tree E A) : tau t = t := rfl

end Isotope.Elgot.ITree
