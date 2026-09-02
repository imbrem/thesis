import Isotope.Elgot.ITree.Basic

/-!
# The polynomial normal form of a visible observation

`Visible E A X` is the polynomial functor `A ⊎ Σ R, E R × (R → X)` in `X`.  This
file makes that presentation explicit: a visible observation is a *shape* — its
constructor together with the event, children erased — and a family of
*children* indexed by the *positions* of that shape.

The point is proof engineering.  Making the branching type `Visible.pos` a
function of the shape turns every dependent transport appearing in the finality
proof into a `cast (congrArg Visible.pos h)` along an `Eq` between shapes, so no
`HEq` occurs anywhere downstream, and definitional proof irrelevance keeps those
casts from being tracked.
-/

namespace Isotope.Elgot.ITree

universe u

variable {E : Type u → Type u} {A X Y : Type (u + 1)}

/-- The head of a visible observation: constructor and event, children erased. -/
abbrev Shape (E : Type u → Type u) (A : Type (u + 1)) : Type (u + 1) := Visible E A PUnit

/-- Erase the children of a visible observation. -/
def Visible.shape : Visible E A X → Shape E A
  | .ret a => .ret a
  | .vis e _ => .vis e (fun _ => PUnit.unit)

/-- The positions (branching index) of a shape: a return branches nowhere, a
visible event branches over its response type. -/
def Visible.pos : Shape E A → Type u
  | .ret _ => PEmpty
  | .vis (R := R) _ _ => R

/-- The children of a visible observation, indexed by the positions of its shape. -/
def Visible.child : (v : Visible E A X) → v.shape.pos → X
  | .ret _ => fun p => p.elim
  | .vis _ k => fun p => k p

/-- Rebuild a visible observation from a shape and a family of children. -/
def Visible.node : (s : Shape E A) → (s.pos → X) → Visible E A X
  | .ret a, _ => .ret a
  | .vis e _, f => .vis e f

/-- The shape of a return. -/
@[simp] theorem Visible.shape_ret (a : A) : (Visible.ret a : Visible E A X).shape = .ret a := rfl

/-- The shape of a visible event. -/
@[simp] theorem Visible.shape_vis {R : Type u} (e : E R) (k : R → X) :
    (Visible.vis e k : Visible E A X).shape = .vis e (fun _ => PUnit.unit) := rfl

/-- Shape/child is a normal form: every visible observation is rebuilt from its own data. -/
@[simp] theorem Visible.node_shape_child (v : Visible E A X) : v.shape.node v.child = v := by
  cases v <;> rfl

/-- `Visible.map` does not disturb the shape. -/
@[simp] theorem Visible.shape_map (f : X → Y) (v : Visible E A X) :
    (Visible.map f v).shape = v.shape := by cases v <;> rfl

/-- `Visible.map` acts on children pointwise, at the very same positions. -/
theorem Visible.child_map (f : X → Y) (v : Visible E A X) (p : (Visible.map f v).shape.pos) :
    (Visible.map f v).child p = f (v.child ((Visible.shape_map f v) ▸ p)) := by
  cases v with
  | ret a => exact p.elim
  | vis e k => rfl

/-- The shape of a rebuilt node is the shape it was built from. -/
@[simp] theorem Visible.shape_node (s : Shape E A) (f : s.pos → X) : (s.node f).shape = s := by
  cases s with
  | ret a => rfl
  | vis e k => cases (funext (fun r => Subsingleton.elim (k r) PUnit.unit) :
      k = fun _ => PUnit.unit); rfl

/-- A shape is its own shape. -/
@[simp] theorem Visible.shape_shape (s : Shape E A) : s.shape = s := by
  cases s with
  | ret a => rfl
  | vis e k =>
      cases (funext (fun r => Subsingleton.elim (k r) PUnit.unit) : k = fun _ => PUnit.unit)
      rfl

/-- Mapping into `PUnit` is exactly shape erasure. -/
@[simp] theorem Visible.map_punit (f : X → PUnit) (w : Visible E A X) :
    Visible.map f w = w.shape := by cases w <;> rfl

/-- `Visible.map` acts on a rebuilt node by postcomposition. -/
@[simp] theorem Visible.map_node (f : X → Y) (s : Shape E A) (g : s.pos → X) :
    Visible.map f (s.node g) = s.node (fun p => f (g p)) := by
  cases s <;> rfl

/-- `Visible.map` in shape/child normal form. -/
theorem Visible.map_eq_node (f : X → Y) (v : Visible E A X) :
    Visible.map f v = v.shape.node (fun p => f (v.child p)) := by
  rw [← Visible.map_node, Visible.node_shape_child]

end Isotope.Elgot.ITree
