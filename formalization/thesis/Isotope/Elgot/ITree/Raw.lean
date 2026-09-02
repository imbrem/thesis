import Isotope.Elgot.ITree.Events

/-!
# Raw, tau-sensitive interaction trees and the erasure onto `Tree`

`Tree E A` is a *weak* model: `tau` is definitionally the identity, so a silent
step is not an observation.  This file supplies the tau-sensitive object that
`Tree E A` is a quotient of, and proves the quotient.

The raw carrier is obtained by making the silent step an ordinary event:
`Raw E A := Tree (Sum1 E TauEv) A`, where `TauEv` is the signature with a single
event whose response is trivial.  Depth in `Tree` is charged at every visible
event, so silent steps are now counted, and equality of raw trees is *strong*
bisimulation for the tau-sensitive functor.  In particular `silent t ≠ t` for
`t = ret a` (`silent_ret_ne`), in sharp contrast to `tau_eq : tau t = t` on the
weak carrier.
-/

namespace Isotope.Elgot.ITree

universe u

/-- The signature with one event, whose response carries no information: the
silent step, reified as an event so that it can be counted. -/
inductive TauEv : Type u → Type u
  | tau : TauEv PUnit.{u + 1}

/-- Raw, tau-sensitive interaction trees: trees over `E` extended by an explicit
silent event.  Equality here counts silent steps. -/
abbrev Raw (E : Type u → Type u) (A : Type (u + 1)) : Type (u + 1) :=
  Tree (Sum1 E TauEv) A

variable {E : Type u → Type u} {A : Type (u + 1)}

/-- The silent event of the extended signature. -/
def tauEvent (E : Type u → Type u) : Sum1 E TauEv PUnit.{u + 1} := Sum1.inr TauEv.tau

/-- One counted silent step. -/
def silent (t : Raw E A) : Raw E A := vis (tauEvent E) (fun _ => t)

/-- A visible `E`-event of a raw tree. -/
def rawVis {R : Type u} (e : E R) (k : R → Raw E A) : Raw E A := vis (Sum1.inl e) k

/-- The head of a silent step. -/
@[simp] theorem destruct_silent (t : Raw E A) :
    (silent t).destruct = Part.some (.vis (tauEvent E) (fun _ => t)) :=
  Tree.destruct_vis _ _

/-- The head of a visible `E`-event. -/
@[simp] theorem destruct_rawVis {R : Type u} (e : E R) (k : R → Raw E A) :
    (rawVis e k).destruct = Part.some (.vis (Sum1.inl e) k) :=
  Tree.destruct_vis _ _

/-- A silent step is *not* invisible on the raw carrier: it is distinguishable
from the computation it delays.  Contrast `tau_eq` on `Tree`. -/
theorem silent_ret_ne (a : A) : silent (ret a : Raw E A) ≠ ret a :=
  Ne.symm (ret_ne_vis a (tauEvent E) _)

/-! ## Divergence by infinite silence -/

/-- The raw tree that steps silently forever.  It is distinct from `diverge`,
which has no head at all. -/
def spin (E : Type u → Type u) (A : Type (u + 1)) : Raw E A :=
  corec (fun _ : PUnit.{u + 2} =>
    Part.some (Visible.vis (tauEvent E) (fun _ => PUnit.unit))) PUnit.unit

/-- `spin` unfolds to one silent step followed by itself. -/
theorem spin_eq_silent : spin E A = silent (spin E A) := by
  refine Tree.eq_vis_of_destruct ?_
  rw [spin, Tree.destruct_corec]
  rfl

/-- `spin` commits to a head — the silent one — so it is not `diverge`. -/
theorem spin_ne_diverge : spin E A ≠ diverge := by
  intro h
  rw [spin_eq_silent] at h
  exact vis_ne_diverge (tauEvent E) _ h


/-! ## Stripping silent steps -/

/-- One step of tau-stripping: a raw tree either has no head at all, or commits
to a visible `E`-head, or consumes one silent step. -/
noncomputable def stepRaw (t : Raw E A) : Option (Visible E A (Raw E A) ⊕ Raw E A) :=
  open Classical in
  if h : t.destruct.Dom then
    some (match t.destruct.get h with
      | .ret a => Sum.inl (Visible.ret a)
      | .vis (Sum1.inl e) c => Sum.inl (Visible.vis e c)
      | .vis (Sum1.inr TauEv.tau) c => Sum.inr (c PUnit.unit))
  else none

/-- A raw tree with no head does not step. -/
@[simp] theorem stepRaw_diverge : stepRaw (diverge : Raw E A) = none := by
  simp only [stepRaw, Tree.destruct_diverge]
  rw [dif_neg (show ¬ (Part.none : Part (Visible (Sum1 E TauEv) A (Raw E A))).Dom from id)]

/-- A return commits immediately. -/
@[simp] theorem stepRaw_ret (a : A) :
    stepRaw (ret a : Raw E A) = some (Sum.inl (Visible.ret a)) := by
  simp only [stepRaw, Tree.destruct_ret]
  rw [dif_pos (show (Part.some (Visible.ret a : Visible (Sum1 E TauEv) A (Raw E A))).Dom
    from trivial)]
  rfl

/-- A visible `E`-event commits immediately. -/
@[simp] theorem stepRaw_rawVis {R : Type u} (e : E R) (k : R → Raw E A) :
    stepRaw (rawVis e k) = some (Sum.inl (Visible.vis e k)) := by
  simp only [stepRaw, destruct_rawVis]
  rw [dif_pos (show (Part.some (Visible.vis (Sum1.inl e) k :
    Visible (Sum1 E TauEv) A (Raw E A))).Dom from trivial)]
  rfl

/-- A silent step is consumed. -/
@[simp] theorem stepRaw_silent (t : Raw E A) : stepRaw (silent t) = some (Sum.inr t) := by
  simp only [stepRaw, destruct_silent]
  rw [dif_pos (show (Part.some (Visible.vis (tauEvent E) (fun _ => t) :
    Visible (Sum1 E TauEv) A (Raw E A))).Dom from trivial)]
  rfl

/-- Strip at most `k` silent steps, looking for a visible head. -/
noncomputable def peel : Nat → Raw E A → Option (Visible E A (Raw E A))
  | 0, _ => none
  | k + 1, t => match stepRaw t with
    | none => none
    | some (Sum.inl v) => some v
    | some (Sum.inr t') => peel k t'

/-- No budget, no head. -/
@[simp] theorem peel_zero (t : Raw E A) : peel 0 t = none := rfl

/-- One step of `peel`. -/
theorem peel_succ (k : Nat) (t : Raw E A) :
    peel (k + 1) t = match stepRaw t with
      | none => none
      | some (Sum.inl v) => some v
      | some (Sum.inr t') => peel k t' := rfl

/-- `peel` on a tree that commits. -/
theorem peel_of_inl {t : Raw E A} {v : Visible E A (Raw E A)}
    (h : stepRaw t = some (Sum.inl v)) (k : Nat) : peel (k + 1) t = some v := by
  rw [peel_succ, h]

/-- `peel` on a tree that steps silently. -/
theorem peel_of_inr {t t' : Raw E A} (h : stepRaw t = some (Sum.inr t')) (k : Nat) :
    peel (k + 1) t = peel k t' := by
  rw [peel_succ, h]

/-- `peel` on a tree with no head. -/
theorem peel_of_none {t : Raw E A} (h : stepRaw t = none) (k : Nat) :
    peel (k + 1) t = none := by
  rw [peel_succ, h]

/-- Increasing the budget never loses a head that has already been found. -/
theorem peel_mono {k : Nat} {t : Raw E A} {v : Visible E A (Raw E A)}
    (h : peel k t = some v) : peel (k + 1) t = some v := by
  induction k generalizing t with
  | zero => simp at h
  | succ k ih =>
      rw [peel_succ] at h
      cases hs : stepRaw t with
      | none => rw [hs] at h; simp at h
      | some r =>
          cases r with
          | inl v' => rw [hs] at h; rw [peel_of_inl hs]; exact h
          | inr t' => rw [hs] at h; rw [peel_of_inr hs]; exact ih h

/-- Any two budgets that find a head find the same one. -/
theorem peel_unique {k l : Nat} {t : Raw E A} {v w : Visible E A (Raw E A)}
    (hv : peel k t = some v) (hw : peel l t = some w) : v = w := by
  have mono : ∀ (m n : Nat) (x : Raw E A) (y : Visible E A (Raw E A)),
      m ≤ n → peel m x = some y → peel n x = some y := by
    intro m n x y hmn
    induction hmn with
    | refl => exact id
    | step _ ih => exact fun hy => peel_mono (ih hy)
  have h1 := mono k (max k l) t v (le_max_left k l) hv
  have h2 := mono l (max k l) t w (le_max_right k l) hw
  rw [h1] at h2
  exact Option.some.inj h2



/-! ## The head of a raw tree, modulo silence -/

/-- The visible head a raw tree eventually commits to, once every silent step
has been stripped.  It is undefined exactly when the tree never commits: either
it has no head at all, or it is silent forever. -/
noncomputable def headPart (t : Raw E A) : Part (Visible E A (Raw E A)) where
  Dom := ∃ v : Visible E A (Raw E A), ∃ k, peel k t = some v
  get h := Classical.choose h

/-- Membership in `headPart` is exactly finding a head within some budget. -/
theorem mem_headPart {t : Raw E A} {v : Visible E A (Raw E A)} :
    v ∈ headPart t ↔ ∃ k, peel k t = some v := by
  constructor
  · rintro ⟨h, rfl⟩
    exact Classical.choose_spec h
  · rintro ⟨k, hk⟩
    refine ⟨⟨v, k, hk⟩, ?_⟩
    obtain ⟨l, hl⟩ := Classical.choose_spec (⟨v, k, hk⟩ : (headPart t).Dom)
    exact peel_unique hl hk

/-- A head found within any budget is *the* head. -/
theorem headPart_eq_some {t : Raw E A} {v : Visible E A (Raw E A)} {k : Nat}
    (h : peel k t = some v) : headPart t = Part.some v := by
  refine Part.ext (fun w => ?_)
  rw [mem_headPart, Part.mem_some_iff]
  constructor
  · rintro ⟨l, hl⟩
    exact (peel_unique h hl).symm
  · rintro rfl
    exact ⟨k, h⟩

/-- A tree that never commits has no head. -/
theorem headPart_eq_none {t : Raw E A} (h : ∀ k, peel k t = none) :
    headPart t = Part.none := by
  refine Part.eq_none_iff.mpr (fun v hv => ?_)
  obtain ⟨k, hk⟩ := mem_headPart.mp hv
  rw [h k] at hk
  simp at hk

/-- The head of a return. -/
@[simp] theorem headPart_ret (a : A) :
    headPart (ret a : Raw E A) = Part.some (Visible.ret a) :=
  headPart_eq_some (peel_of_inl (stepRaw_ret a) 0)

/-- The head of a visible `E`-event. -/
@[simp] theorem headPart_rawVis {R : Type u} (e : E R) (k : R → Raw E A) :
    headPart (rawVis e k) = Part.some (Visible.vis e k) :=
  headPart_eq_some (peel_of_inl (stepRaw_rawVis e k) 0)

/-- A tree with no head at all has no head modulo silence either. -/
@[simp] theorem headPart_diverge : headPart (diverge : Raw E A) = Part.none :=
  headPart_eq_none (fun k => by cases k with
    | zero => rfl
    | succ k => exact peel_of_none stepRaw_diverge k)

/-- Silent steps do not change the head: this is the whole point. -/
@[simp] theorem headPart_silent (t : Raw E A) : headPart (silent t) = headPart t := by
  refine Part.ext (fun v => ?_)
  rw [mem_headPart, mem_headPart]
  constructor
  · rintro ⟨k, hk⟩
    cases k with
    | zero => simp at hk
    | succ k => exact ⟨k, by rwa [peel_of_inr (stepRaw_silent t)] at hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨k + 1, by rw [peel_of_inr (stepRaw_silent t)]; exact hk⟩

/-- `spin` steps silently, forever. -/
@[simp] theorem stepRaw_spin : stepRaw (spin E A) = some (Sum.inr (spin E A)) := by
  conv_lhs => rw [spin_eq_silent]
  exact stepRaw_silent _

/-- No budget suffices to find a head of `spin`. -/
theorem peel_spin (k : Nat) : peel k (spin E A) = none := by
  induction k with
  | zero => rfl
  | succ k ih => rw [peel_of_inr stepRaw_spin]; exact ih

/-- Infinite silence has no head. -/
@[simp] theorem headPart_spin : headPart (spin E A) = Part.none :=
  headPart_eq_none peel_spin

/-! ## Erasure onto the weak carrier -/

/-- Erase silent steps.  This is the canonical map from raw, tau-sensitive
interaction trees onto the weak carrier, defined by corecursion on `headPart`. -/
noncomputable def erase (t : Raw E A) : Tree E A := corec headPart t

/-- `erase` is a coalgebra morphism from `headPart` to `Tree.destruct`. -/
theorem destruct_erase (t : Raw E A) :
    (erase t).destruct = Visible.map erase <$> headPart t := Tree.destruct_corec _ _

/-- Trees with the same head modulo silence have the same erasure. -/
theorem erase_congr {x y : Raw E A} (h : headPart x = headPart y) : erase x = erase y := by
  rw [← Tree.construct_destruct (erase x), ← Tree.construct_destruct (erase y),
    destruct_erase, destruct_erase, h]

/-- Erasing a return. -/
@[simp] theorem erase_ret (a : A) : erase (ret a : Raw E A) = ret a := by
  rw [← Tree.construct_destruct (erase (ret a : Raw E A)), destruct_erase, headPart_ret]
  simp

/-- Erasing a visible `E`-event. -/
@[simp] theorem erase_rawVis {R : Type u} (e : E R) (k : R → Raw E A) :
    erase (rawVis e k) = vis e (fun r => erase (k r)) := by
  rw [← Tree.construct_destruct (erase (rawVis e k)), destruct_erase, headPart_rawVis]
  simp [Visible.map, Function.comp_def]

/-- Erasing a headless tree. -/
@[simp] theorem erase_diverge : erase (diverge : Raw E A) = diverge := by
  rw [← Tree.construct_destruct (erase (diverge : Raw E A)), destruct_erase, headPart_diverge]
  simp

/-- A silent step is erased: this is tau-insensitivity of the weak carrier. -/
@[simp] theorem erase_silent (t : Raw E A) : erase (silent t) = erase t :=
  erase_congr (headPart_silent t)

/-- Infinite silence erases to silent divergence: the two notions of divergence
are identified by the quotient, though they are distinct raw trees. -/
@[simp] theorem erase_spin : erase (spin E A) = diverge := by
  rw [← Tree.construct_destruct (erase (spin E A)), destruct_erase, headPart_spin]
  simp



/-! ## The section: weak trees as raw trees with no silent steps -/

/-- Read a weak tree as a raw tree with no silent steps, by relabelling its
events into the extended signature. -/
def emb (t : Tree E A) : Raw E A := translate (Sum1.inl1 E TauEv) t

/-- `emb` preserves returns. -/
@[simp] theorem emb_ret (a : A) : emb (ret a : Tree E A) = ret a := translate_ret _ a

/-- `emb` preserves divergence. -/
@[simp] theorem emb_diverge : emb (diverge : Tree E A) = diverge := translate_diverge _

/-- `emb` sends a visible event to the corresponding raw visible event. -/
@[simp] theorem emb_vis {R : Type u} (e : E R) (k : R → Tree E A) :
    emb (vis e k) = rawVis e (fun r => emb (k r)) := translate_vis _ e k

/-- Erasure is a retraction of `emb`: a tree with no silent steps is unchanged
by stripping silent steps. -/
theorem erase_emb (t : Tree E A) : erase (emb t) = t := by
  refine Tree.eq_of_bisim' (fun x y => x = erase (emb y)) ?_ rfl
  rintro x y rfl
  rcases Tree.cases_three y with rfl | ⟨a, rfl⟩ | ⟨R, e, k, rfl⟩
  · exact Or.inl ⟨by simp, by simp⟩
  · exact Or.inr (Or.inl ⟨a, by simp, by simp⟩)
  · exact Or.inr (Or.inr ⟨R, e, (fun r => erase (emb (k r))), k,
      by simp, by simp, fun s => rfl⟩)

/-- Every weak tree is the erasure of a raw tree. -/
theorem erase_surjective : Function.Surjective (erase (E := E) (A := A)) :=
  fun t => ⟨emb t, erase_emb t⟩

/-! ## The quotient -/

/-- Weak bisimulation of raw trees: they commit to the same visible heads in the
same order, ignoring how many silent steps separate them.  Concretely, they have
the same erasure. -/
def Weak (x y : Raw E A) : Prop := erase x = erase y

/-- Weak bisimulation of raw trees is exactly bisimulation of their erasures. -/
theorem weak_iff_bisim {x y : Raw E A} : Weak x y ↔ Bisim (erase x) (erase y) :=
  bisim_iff_eq.symm

/-- Weak bisimulation is an equivalence relation. -/
def weakSetoid (E : Type u → Type u) (A : Type (u + 1)) : Setoid (Raw E A) where
  r := Weak
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

/-- **The weak carrier is the quotient of the raw carrier.**  `erase` and `emb`
exhibit `Tree E A` as `Raw E A` modulo weak bisimulation. -/
noncomputable def rawQuotientEquiv (E : Type u → Type u) (A : Type (u + 1)) :
    Quotient (weakSetoid E A) ≃ Tree E A where
  toFun := Quotient.lift erase (fun _ _ h => h)
  invFun t := Quotient.mk (weakSetoid E A) (emb t)
  left_inv := by
    rintro ⟨x⟩
    exact Quotient.sound (show erase (emb (erase x)) = erase x from erase_emb _)
  right_inv := erase_emb

/-! ## The quotient is proper -/

/-- Silent steps are identified by the quotient. -/
theorem weak_silent (t : Raw E A) : Weak (silent t) t := erase_silent t

/-- Infinite silence and headlessness are identified by the quotient. -/
theorem weak_spin_diverge : Weak (spin E A) diverge := by
  simp [Weak]

/-- ...but they are different raw trees: the quotient is not trivial. -/
theorem spin_ne_diverge' : spin E A ≠ (diverge : Raw E A) := spin_ne_diverge

/-- The quotient really quotients: weak bisimulation is strictly coarser than
equality of raw trees, already on returns. -/
theorem weak_ne_eq (a : A) :
    ∃ x y : Raw E A, Weak x y ∧ x ≠ y :=
  ⟨silent (ret a), ret a, weak_silent _, silent_ret_ne a⟩

/-- A second, divergence-flavoured witness that the quotient is proper. -/
theorem weak_ne_eq_diverge : ∃ x y : Raw E A, Weak x y ∧ x ≠ y :=
  ⟨spin E A, diverge, weak_spin_diverge, spin_ne_diverge⟩

/-! ## The operations respect the relation -/

/-- Visible events are a congruence for weak bisimulation. -/
theorem weak_congr_rawVis {R : Type u} (e : E R) {k l : R → Raw E A}
    (h : ∀ r, Weak (k r) (l r)) : Weak (rawVis e k) (rawVis e l) := by
  simp only [Weak, erase_rawVis]
  exact congrArg (vis e) (funext fun r => h r)

/-- Silent steps are a congruence for weak bisimulation. -/
theorem weak_congr_silent {x y : Raw E A} (h : Weak x y) : Weak (silent x) (silent y) := by
  simp only [Weak, erase_silent]
  exact h

/-- A silent step may be deleted on the left of a weak bisimulation. -/
theorem weak_silent_left {x y : Raw E A} (h : Weak x y) : Weak (silent x) y := by
  simp only [Weak, erase_silent]
  exact h


end Isotope.Elgot.ITree
