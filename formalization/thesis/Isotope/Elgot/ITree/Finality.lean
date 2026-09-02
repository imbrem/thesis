import Isotope.Elgot.ITree.Shape
import Mathlib.Logic.Equiv.Defs

/-!
# Finality of the interaction-tree coalgebra

`Tree E A` is the limit of the terminal chain `PUnit ← F PUnit ← F² PUnit ← …`
for the *visible-commitment* functor `F = Part ∘ Visible E A`.  This file proves
that this limit really is the final `F`-coalgebra, by exhibiting the structure
map `Tree.destruct` inverse to `construct` and deriving the universal property.

Two structural facts make the argument go through, both consequences of the
weak (tau-insensitive) presentation:

* **silence is permanent**: `Part.map` never changes `Dom`, so coherence forces
  every observation of a tree to have the same domain (`Tree.dom_observe`).
  `Part.none` means "no visible head, ever", not "decide later"; this is what
  makes `destruct` total.
* **shape is pinned at depth one**: `Visible` is polynomial and `Visible.map`
  cannot change shape, so the head constructor — and for `vis` the response
  type and event — is already determined by `t.observe 1` (`Tree.shape_get`).

Nothing here is classical: `Tree.destruct` is a genuine computable definition,
and the finality results depend only on `propext` and `Quot.sound`.

This is a separate construction rather than a corollary of `corec_unique`, and
necessarily so: `corec_hyp_iff` shows `corec`/`corec_unique` say exactly that
`(Tree E A, construct)` is a *corecursive algebra*, and
`corecursive_not_lambek` exhibits a corecursive algebra whose structure map is
not injective.  So Lambek's lemma is not available from `corec_unique` alone.
-/

namespace Isotope.Elgot.ITree

universe u

variable {E : Type u → Type u} {A X Y : Type (u + 1)}

/-! ## Packaging one unfolding step -/

/-- Package a one-step unfolding as a tree: the algebra half of finality. -/
def construct (v : Part (Visible E A (Tree E A))) : Tree E A where
  observe
    | 0 => PUnit.unit
    | n + 1 => Visible.map (fun t => t.observe n) <$> v
  coherent
    | 0 => rfl
    | n + 1 => by
        simp only [Approx.truncate, Part.map_eq_map, Part.map_map]
        congr 1
        funext w
        rw [Function.comp_apply, Visible.map_comp]
        congr 1
        funext t
        exact t.coherent n

/-- The observations of `construct`. -/
@[simp] theorem observe_construct (v : Part (Visible E A (Tree E A))) (n : Nat) :
    (construct v).observe (n + 1) = Visible.map (fun t => t.observe n) <$> v := rfl

/-- Constructing from no visible head is silent divergence. -/
@[simp] theorem construct_none : construct (E := E) (A := A) Part.none = diverge := by
  ext n; cases n
  · rfl
  · simp [observe_construct, observe_diverge]

/-- Constructing from a return head is `ret`. -/
@[simp] theorem construct_ret (a : A) :
    construct (E := E) (Part.some (.ret a)) = ret a := by
  ext n; cases n <;> rfl

/-- Constructing from a visible-event head is `vis`. -/
@[simp] theorem construct_vis {R : Type u} (e : E R) (k : R → Tree E A) :
    construct (Part.some (.vis e k)) = vis e k := by
  ext n; cases n <;> rfl

/-- `corec` unfolds one step through `construct`. -/
theorem corec_construct (h : X → Part (Visible E A X)) (x : X) :
    corec h x = construct (Visible.map (corec h) <$> h x) := by
  ext n; cases n with
  | zero => rfl
  | succ n =>
      rw [observe_corec, observe_construct]
      simp only [Part.map_eq_map, Part.map_map]
      congr 1
      funext w
      rw [Function.comp_apply, Visible.map_comp]
      rfl

/-! ## Shape propagation along the observation family -/

/-- Equal partial values have equal contents, at any two domain proofs.  This is
the congruence `Part.get` lacks: `Part.get` is dependent in its domain proof, so
rewriting underneath it fails the motive check. -/
theorem partGetCongr {α : Type _} {o o' : Part α} (e : o = o') (d : o.Dom) (d' : o'.Dom) :
    o.get d = o'.get d' := by cases e; rfl

/-- Truncation does not change the domain of an observation. -/
theorem Approx.dom_truncate (n : Nat) (x : Approx E A (n + 2)) :
    (Approx.truncate (n + 1) x).Dom = x.Dom := rfl

/-- Truncation acts on the visible node by `Visible.map`. -/
theorem Approx.get_truncate (n : Nat) (x : Approx E A (n + 2)) (h : x.Dom) :
    (Approx.truncate (n + 1) x).get h = Visible.map (Approx.truncate n) (x.get h) := rfl

/-- Silence is permanent: every observation of a tree has the same domain. -/
theorem Tree.dom_observe (t : Tree E A) (n : Nat) :
    (t.observe (n + 1)).Dom = (t.observe 1).Dom := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [← ih, ← Approx.dom_truncate n (t.observe (n + 2)), t.coherent (n + 1)]

/-- The head domain of a tree propagates to every depth. -/
theorem Tree.dom_of_head (t : Tree E A) (h : (t.observe 1).Dom) (n : Nat) :
    (t.observe (n + 1)).Dom := cast (t.dom_observe n).symm h

/-- Every observation of a tree exposes the head shape recorded at depth one. -/
theorem Tree.shape_get (t : Tree E A) (n : Nat) (hn : (t.observe (n + 1)).Dom)
    (h : (t.observe 1).Dom) :
    Visible.shape ((t.observe (n + 1)).get hn) = (t.observe 1).get h := by
  induction n with
  | zero => exact Visible.shape_shape _
  | succ n ih =>
      have hn' : (t.observe (n + 1)).Dom := t.dom_of_head h n
      rw [← ih hn']
      have e1 : (t.observe (n + 1)).get hn'
          = (Approx.truncate (n + 1) (t.observe (n + 2))).get hn :=
        (partGetCongr (t.coherent (n + 1)) hn hn').symm
      rw [e1, Approx.get_truncate, Visible.shape_map]

/-! ## Transport of positions -/

/-- Transporting a position across `Visible.map` commutes with taking children. -/
theorem Visible.child_map_cast {X Y : Type (u + 1)} (f : X → Y) (v : Visible E A X)
    (s : Shape E A) (hv : v.shape = s) (hw : (Visible.map f v).shape = s) (p : s.pos) :
    (Visible.map f v).child (cast (congrArg Visible.pos hw.symm) p)
      = f (v.child (cast (congrArg Visible.pos hv.symm) p)) := by
  cases hv
  cases v with
  | ret a => exact PEmpty.elim p
  | vis e k => rfl

/-- Transport of a position is independent of the proof of the shape equation. -/
theorem Visible.cast_pos_irrel {v : Visible E A X} {s : Shape E A}
    (h₁ h₂ : s = v.shape) (p : s.pos) :
    cast (congrArg Visible.pos h₁) p = cast (congrArg Visible.pos h₂) p := rfl

/-- Equal visible nodes have equal children, at any two proofs of the same shape. -/
theorem Visible.child_congr {v w : Visible E A X} (e : v = w) {s : Shape E A}
    (hv : v.shape = s) (hw : w.shape = s) (p : s.pos) :
    v.child (cast (congrArg Visible.pos hv.symm) p)
      = w.child (cast (congrArg Visible.pos hw.symm) p) := by
  cases e; rfl

/-- A visible node is rebuilt from any shape equal to its own. -/
theorem Visible.node_cast_child (v : Visible E A X) (s : Shape E A) (hv : v.shape = s) :
    s.node (fun p => v.child (cast (congrArg Visible.pos hv.symm) p)) = v := by
  cases hv; exact Visible.node_shape_child v

/-- Rebuilding a node along an equality of shapes. -/
theorem Visible.node_cast {s s' : Shape E A} (hs : s = s') (g : s'.pos → X) :
    s.node (fun p => g (cast (congrArg Visible.pos hs) p)) = s'.node g := by
  cases hs; rfl

/-! ## The tail of a tree -/

/-- The subtree of `t` at head position `p`, observed to depth `n`. -/
def Tree.childApprox (t : Tree E A) (h : (t.observe 1).Dom)
    (p : ((t.observe 1).get h).pos) : (n : Nat) → Approx E A n
  | 0 => PUnit.unit
  | n + 1 =>
      Visible.child ((t.observe (n + 2)).get (t.dom_of_head h (n + 1)))
        (cast (congrArg Visible.pos
          (t.shape_get (n + 1) (t.dom_of_head h (n + 1)) h).symm) p)

/-- The observations of a subtree are coherent. -/
theorem Tree.truncate_childApprox (t : Tree E A) (h : (t.observe 1).Dom)
    (p : ((t.observe 1).get h).pos) (n : Nat) :
    Approx.truncate n (t.childApprox h p (n + 1)) = t.childApprox h p n := by
  cases n with
  | zero => rfl
  | succ n =>
      change Approx.truncate (n + 1) (Visible.child _ _) = Visible.child _ _
      have hv₃ : ((t.observe (n + 3)).get (t.dom_of_head h (n + 2))).shape
          = (t.observe 1).get h := t.shape_get (n + 2) _ h
      have hw : (Visible.map (Approx.truncate (n + 1))
            ((t.observe (n + 3)).get (t.dom_of_head h (n + 2)))).shape
          = (t.observe 1).get h := by rw [Visible.shape_map]; exact hv₃
      have e : (t.observe (n + 2)).get (t.dom_of_head h (n + 1))
          = Visible.map (Approx.truncate (n + 1))
              ((t.observe (n + 3)).get (t.dom_of_head h (n + 2))) := by
        rw [← Approx.get_truncate]
        exact partGetCongr (t.coherent (n + 2)).symm _ _
      exact ((Visible.child_congr e (t.shape_get (n + 1) _ h) hw p).trans
        (Visible.child_map_cast _ _ _ hv₃ hw p)).symm

/-- The subtree of `t` at head position `p`. -/
def Tree.child (t : Tree E A) (h : (t.observe 1).Dom)
    (p : ((t.observe 1).get h).pos) : Tree E A where
  observe := t.childApprox h p
  coherent := t.truncate_childApprox h p

/-- A subtree's observations are the children of the corresponding observation of `t`. -/
theorem Tree.childApprox_eq (t : Tree E A) (h : (t.observe 1).Dom)
    (p : ((t.observe 1).get h).pos) (n : Nat) (hn : (t.observe (n + 1)).Dom) :
    t.childApprox h p n
      = ((t.observe (n + 1)).get hn).child
          (cast (congrArg Visible.pos (t.shape_get n hn h).symm) p) := by
  cases n with
  | zero => rfl
  | succ n => rfl

/-! ## The structure map -/

/-- The unique one-step unfolding of a tree: the coalgebra half of finality. -/
def Tree.destruct (t : Tree E A) : Part (Visible E A (Tree E A)) where
  Dom := (t.observe 1).Dom
  get h := ((t.observe 1).get h).node (fun p => t.child h p)

/-- `destruct` is defined exactly where the depth-one observation is. -/
@[simp] theorem Tree.destruct_dom (t : Tree E A) : t.destruct.Dom = (t.observe 1).Dom := rfl

/-- The visible head exposed by `destruct`. -/
@[simp] theorem Tree.destruct_get (t : Tree E A) (h : t.destruct.Dom) :
    t.destruct.get h = ((t.observe 1).get h).node (fun p => t.child h p) := rfl

/-- `construct` undoes `destruct`: every tree is its own one-step unfolding. -/
theorem Tree.construct_destruct (t : Tree E A) : construct t.destruct = t := by
  ext n
  cases n with
  | zero => rfl
  | succ n =>
      rw [observe_construct]
      refine Part.ext' (Iff.of_eq (t.dom_observe n).symm) (fun h hn => ?_)
      change Visible.map (fun s => s.observe n) (t.destruct.get h) = (t.observe (n + 1)).get hn
      rw [Tree.destruct_get, Visible.map_node]
      refine Eq.trans ?_
        (Visible.node_cast_child ((t.observe (n + 1)).get hn) _ (t.shape_get n hn h))
      exact congrArg (Visible.node ((t.observe 1).get h))
        (funext fun p => t.childApprox_eq h p n hn)

section Construct

variable (v : Part (Visible E A (Tree E A))) (h : ((construct v).observe 1).Dom)

/-- The head shape of `construct v` is the shape of `v`. -/
theorem Tree.shape_head_construct :
    (v.get h).shape = ((construct v).observe 1).get h := rfl

/-- The subtrees of `construct v` are the subtrees packaged into `v`. -/
theorem Tree.child_construct (p : (((construct v).observe 1).get h).pos) :
    (construct v).child h p
      = (v.get h).child
          (cast (congrArg Visible.pos (Tree.shape_head_construct v h).symm) p) := by
  ext n
  cases n with
  | zero => rfl
  | succ n =>
      have hw : (Visible.map (fun t : Tree E A => t.observe (n + 1)) (v.get h)).shape
          = ((construct v).observe 1).get h :=
        (Visible.shape_map _ (v.get h)).trans (Tree.shape_head_construct v h)
      exact Visible.child_map_cast (fun t : Tree E A => t.observe (n + 1)) (v.get h) _
        (Tree.shape_head_construct v h) hw p

/-- `destruct` undoes `construct`. -/
theorem Tree.destruct_construct : (construct v).destruct = v := by
  refine Part.ext' Iff.rfl (fun h₁ h₂ => ?_)
  rw [Tree.destruct_get]
  refine Eq.trans ?_ (Visible.node_cast_child (v.get h₂) _ (Tree.shape_head_construct v h₁))
  exact congrArg (Visible.node (((construct v).observe 1).get h₁))
    (funext fun p => Tree.child_construct v h₁ p)

end Construct

/-! ## Finality -/

/-- Finality: the carrier is isomorphic to one layer of `Part ∘ Visible`. -/
def Tree.destructEquiv (E : Type u → Type u) (A : Type (u + 1)) :
    Tree E A ≃ Part (Visible E A (Tree E A)) where
  toFun := Tree.destruct
  invFun := construct
  left_inv := Tree.construct_destruct
  right_inv := Tree.destruct_construct

/-- Silent divergence has no visible head. -/
@[simp] theorem Tree.destruct_diverge : (diverge (E := E) (A := A)).destruct = Part.none := by
  rw [← construct_none]; exact Tree.destruct_construct _

/-- The head of a return. -/
@[simp] theorem Tree.destruct_ret (a : A) :
    (ret (E := E) a).destruct = Part.some (.ret a) := by
  rw [← construct_ret]; exact Tree.destruct_construct _

/-- The head of a visible event. -/
@[simp] theorem Tree.destruct_vis {R : Type u} (e : E R) (k : R → Tree E A) :
    (vis e k).destruct = Part.some (.vis e k) := by
  rw [← construct_vis]; exact Tree.destruct_construct _

/-- `corec h` is a coalgebra morphism. -/
theorem Tree.destruct_corec (h : X → Part (Visible E A X)) (x : X) :
    (corec h x).destruct = Visible.map (corec h) <$> h x := by
  rw [corec_construct h x]; exact Tree.destruct_construct _

/-- `corec h` is the *unique* coalgebra morphism into the final coalgebra. -/
theorem Tree.corec_unique_destruct (h : X → Part (Visible E A X)) (F : X → Tree E A)
    (hF : ∀ x, (F x).destruct = Visible.map F <$> h x) : F = corec h := by
  refine corec_unique h F (fun x n => ?_)
  conv_lhs => rw [← Tree.construct_destruct (F x), hF x]
  rw [observe_construct]
  simp only [Part.map_eq_map, Part.map_map]
  exact congrArg (fun g => Part.map g (h x))
    (funext fun w => Visible.map_comp F (fun t => t.observe n) w)

/-- Finality, packaged: every `Part ∘ Visible E A`-coalgebra has a unique
morphism into `Tree E A`. -/
theorem Tree.existsUnique_coalgebraHom (h : X → Part (Visible E A X)) :
    ∃! F : X → Tree E A, ∀ x, (F x).destruct = Visible.map F <$> h x :=
  ⟨corec h, Tree.destruct_corec h, fun F hF => Tree.corec_unique_destruct h F hF⟩

/-- Lambek: the identity is the unfolding of the final coalgebra structure. -/
theorem Tree.corec_destruct : corec (Tree.destruct (E := E) (A := A)) = id :=
  (Tree.corec_unique_destruct _ id (fun t =>
    ((Part.map_eq_map (Visible.map (id : Tree E A → Tree E A)) t.destruct).trans
      (Part.map_id' Visible.map_id t.destruct)).symm)).symm

/-! ## Case analysis -/

/-- Every tree is silent divergence, a return, or a visible event. -/
theorem Tree.cases_three (t : Tree E A) :
    t = diverge ∨ (∃ a : A, t = ret a) ∨
      (∃ (R : Type u) (e : E R) (k : R → Tree E A), t = vis e k) := by
  have ht : construct t.destruct = t := Tree.construct_destruct t
  by_cases hd : t.destruct.Dom
  · rw [← Part.some_get hd] at ht
    cases hv : t.destruct.get hd with
    | ret a => exact Or.inr (Or.inl ⟨a, by rw [← ht, hv, construct_ret]⟩)
    | vis e k => exact Or.inr (Or.inr ⟨_, e, k, by rw [← ht, hv, construct_vis]⟩)
  · rw [Part.eq_none_iff'.mpr hd, construct_none] at ht
    exact Or.inl ht.symm

/-- A tree has no visible head exactly when it diverges. -/
theorem Tree.destruct_eq_none_iff (t : Tree E A) : t.destruct = Part.none ↔ t = diverge := by
  constructor
  · intro h; rw [← Tree.construct_destruct t, h, construct_none]
  · rintro rfl; exact Tree.destruct_diverge

/-! ## Coinduction through `destruct` -/

/-- Coinduction: a `destruct`-bisimulation is contained in equality.  Two related
trees must agree on whether they have a visible head, on its shape, and be
related again at every child position. -/
theorem Tree.eq_of_bisim (R : Tree E A → Tree E A → Prop)
    (hR : ∀ x y, R x y → ∃ ed : x.destruct.Dom = y.destruct.Dom,
      ∀ hx : x.destruct.Dom, ∃ es : (x.destruct.get hx).shape
          = (y.destruct.get (cast ed hx)).shape,
        ∀ p, R ((x.destruct.get hx).child p)
          ((y.destruct.get (cast ed hx)).child (cast (congrArg Visible.pos es) p)))
    {x y : Tree E A} (h : R x y) : x = y := by
  suffices hall : ∀ (n : Nat) (x y : Tree E A), R x y → x.observe n = y.observe n from
    Tree.ext (fun n => hall n x y h)
  intro n
  induction n with
  | zero => intro x y _; rfl
  | succ n ih =>
      intro x y hxy
      obtain ⟨ed, hs⟩ := hR x y hxy
      rw [← Tree.construct_destruct x, ← Tree.construct_destruct y]
      simp only [observe_construct]
      refine Part.ext' (Iff.of_eq ed) (fun h₁ h₂ => ?_)
      obtain ⟨es, hchild⟩ := hs h₁
      change Visible.map (fun t : Tree E A => t.observe n) (x.destruct.get h₁)
        = Visible.map (fun t : Tree E A => t.observe n) (y.destruct.get h₂)
      rw [Visible.map_eq_node, Visible.map_eq_node]
      refine Eq.trans ?_
        (Visible.node_cast es (fun p => ((y.destruct.get h₂).child p).observe n))
      exact congrArg (Visible.node ((x.destruct.get h₁).shape))
        (funext fun p => ih _ _ (hchild p))

/-! ## Why finality is a separate construction -/

/-- The hypothesis of `corec_unique` is exactly the `construct`-fixpoint
equation.  So `corec`/`corec_unique` say precisely that `(Tree E A, construct)`
is a *corecursive algebra*, which is strictly weaker than terminality: see
`corecursive_not_lambek`. -/
theorem corec_hyp_iff (h : X → Part (Visible E A X)) (F : X → Tree E A) :
    (∀ (x : X) (n : Nat),
        (F x).observe (n + 1) = Visible.map (fun y => (F y).observe n) <$> h x)
      ↔ (∀ x, F x = construct (Visible.map F <$> h x)) := by
  constructor
  · intro hyp x
    apply Tree.ext
    intro n
    cases n with
    | zero => rfl
    | succ n =>
      rw [hyp x n, observe_construct]
      simp only [Part.map_eq_map, Part.map_map, Visible.map_comp, Function.comp_def]
  · intro hyp x n
    rw [hyp x, observe_construct]
    simp only [Part.map_eq_map, Part.map_map, Visible.map_comp, Function.comp_def]

/-- Corecursive-algebra structure does *not* imply the structure map is
injective, so Lambek's lemma is unavailable from `corec_unique` alone: take
`F X = Option X` with carrier `PUnit`.  This is why `Tree.destruct` has to be
constructed by hand rather than inverted out of `corec_unique`. -/
theorem corecursive_not_lambek :
    ∃ b : Option PUnit → PUnit,
      (∀ (X : Type) (h : X → Option X),
          ∃! F : X → PUnit, ∀ x, F x = b (Option.map F (h x)))
        ∧ ¬ Function.Injective b := by
  refine ⟨fun _ => PUnit.unit, ?_, ?_⟩
  · intro X h
    refine ⟨fun _ => PUnit.unit, fun x => rfl, ?_⟩
    intro F _
    funext x
    exact rfl
  · intro hinj
    have := hinj (a₁ := none) (a₂ := some PUnit.unit) rfl
    cases this

end Isotope.Elgot.ITree
