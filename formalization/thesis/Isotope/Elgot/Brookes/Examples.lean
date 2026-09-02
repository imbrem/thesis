import Isotope.Elgot.Brookes.SeqCst
import Isotope.Elgot.Brookes.Compare

/-!
# Representative Brookes computations

Generic looping examples first, then the sequentially consistent reads, writes,
sequencing and loops promised by the issue.  Everything here is a *separation*
result or an explicit witness: the point of a denotational model is that it
distinguishes computations, so each example either exhibits a trace or shows one
is impossible.
-/

namespace Isotope.Elgot

universe u

namespace Brookes

variable {E : Type u} {c : Rewriting E} {A B : Type u}

/-! ## Looping -/

theorem approx_pure_inr (a : A) :
    ∀ n : Nat, approx (fun a : A ↦ (pure (Sum.inr a) : Brookes c (B ⊕ A))) n a = ⊥ := by
  intro n
  induction n generalizing a with
  | zero => rfl
  | succ n ih => rw [approx_succ, pure_bind_eq]; exact ih a

/-- Partial correctness: a body that always recurses denotes `⊥`, even though
every unfolding is productive of no trace.  Divergence is not observable. -/
@[simp] theorem iter_forever (a : A) :
    iter (B := B) (fun a : A ↦ (pure (Sum.inr a) : Brookes c (B ⊕ A))) a = ⊥ :=
  le_antisymm (iter_le _ a fun n ↦ le_of_eq (approx_pure_inr a n)) bot_le

/-- A body with no executions at all also denotes `⊥`. -/
@[simp] theorem iter_bot (a : A) :
    iter (fun _ : A ↦ (⊥ : Brookes c (B ⊕ A))) a = (⊥ : Brookes c B) := by
  refine le_antisymm (iter_le _ a fun n ↦ ?_) bot_le
  cases n with
  | zero => exact le_rfl
  | succ n => rw [approx_succ, bot_bind]

/-- A body that returns immediately denotes exactly that return. -/
@[simp] theorem iter_immediate (a : A) (b : B) :
    iter (fun _ : A ↦ (pure (Sum.inl b) : Brookes c (B ⊕ A))) a = (pure b : Brookes c B) := by
  have key : ∀ n : Nat, approx (fun _ : A ↦ (pure (Sum.inl b) : Brookes c (B ⊕ A))) (n + 1) a
      = (pure b : Brookes c B) := by
    intro n
    rw [approx_succ, pure_bind_eq]
    rfl
  refine le_antisymm (iter_le _ a fun n ↦ ?_) ?_
  · cases n with
    | zero => exact bot_le
    | succ n => exact le_of_eq (key n)
  · exact (key 0) ▸ approx_le_iter _ 1 a

end Brookes

namespace Brookes

namespace SeqCst

open Isotope.Elgot.Brookes

variable {Loc Val : Type u}

/-! ## Sequencing -/

/-- `st-st`: a write followed by a write to the same location is refined by the
second write alone.  The witness is a mumble across the sequencing seam. -/
theorem write_le_write_write [DecidableEq Loc] (ℓ : Loc) (v w : Val) :
    write ℓ w ≤ (write ℓ v >>= fun _ ↦ write ℓ w : Comp Loc Val PUnit) := by
  apply Brookes.le_of_mem
  intro t x hx
  obtain ⟨μ, hr⟩ := (mem_write_iff ℓ w t x).1 hx
  refine (Brookes.mem_bind_iff _ _ t x).2
    ⟨PUnit.unit, [(μ, Function.update μ ℓ v)],
      [(Function.update μ ℓ v, Function.update (Function.update μ ℓ v) ℓ w)],
      mem_write ℓ v μ, mem_write ℓ w _, ?_⟩
  refine Relation.ReflTransGen.trans ?_ hr
  rw [← Function.update_idem v w μ]
  exact Relation.ReflTransGen.single (Step.mumble _ _ _ [])

/-- `st-ld`: reading back a location just written returns the written value.
The read's stutter step is mumbled into the write's transition. -/
theorem write_pure_le_write_read [DecidableEq Loc] (ℓ : Loc) (v : Val) :
    (write ℓ v >>= fun _ ↦ (pure v : Comp Loc Val Val))
      ≤ (write ℓ v >>= fun _ ↦ read ℓ) := by
  apply Brookes.le_of_mem
  intro t x hx
  obtain ⟨a, u, w, hu, hw, hr⟩ := (Brookes.mem_bind_iff _ _ t x).1 hx
  obtain ⟨hxv, hw0⟩ := (Brookes.mem_pure_iff v x w).1 hw
  rw [hxv]
  obtain ⟨μ, hru⟩ := (mem_write_iff ℓ v u a).1 hu
  have hu_t : (rewriting (Store Loc Val)).Refines u t := by
    refine Relation.ReflTransGen.trans ?_ hr
    have h1 := Rewriting.refines_appendLeft (c := rewriting (Store Loc Val)) u hw0
    rwa [List.append_nil] at h1
  have hread : ([(Function.update μ ℓ v, Function.update μ ℓ v)], v) ∈ read (Val := Val) ℓ := by
    have := mem_read ℓ (Function.update μ ℓ v)
    rwa [Function.update_self] at this
  refine (Brookes.mem_bind_iff _ _ t v).2
    ⟨PUnit.unit, [(μ, Function.update μ ℓ v)],
      [(Function.update μ ℓ v, Function.update μ ℓ v)], mem_write ℓ v μ, hread, ?_⟩
  refine Relation.ReflTransGen.trans ?_ (hru.trans hu_t)
  exact Relation.ReflTransGen.single (Step.mumble _ _ _ [])

/-! ## Reads and interference -/

/-- Two consecutive reads of the same location, paired. -/
def readTwice (ℓ : Loc) : Comp Loc Val (Val × Val) :=
  read ℓ >>= fun x ↦ read ℓ >>= fun y ↦ pure (x, y)

/-- A single read, duplicated: the interference-free reading of `readTwice`. -/
def readOnce (ℓ : Loc) : Comp Loc Val (Val × Val) :=
  read ℓ >>= fun x ↦ pure (x, x)

/-- Interference is observable: the two reads may disagree. -/
theorem mem_readTwice_disagree (ℓ : Loc) (μ ν : Store Loc Val) :
    ([(μ, μ)] ++ ([(ν, ν)] ++ []), (μ ℓ, ν ℓ)) ∈ readTwice ℓ :=
  Brookes.mem_bind _ _ (mem_read ℓ μ) (Brookes.mem_bind _ _ (mem_read ℓ ν) (Brookes.mem_pure _))

/-- Consequently `read` is not idempotent: `readTwice` is not refined by
`readOnce` as soon as two states disagree at `ℓ`. -/
theorem readTwice_not_le_readOnce (ℓ : Loc) (μ ν : Store Loc Val) (h : μ ℓ ≠ ν ℓ) :
    ¬ readTwice (Val := Val) ℓ ≤ readOnce ℓ := by
  intro hle
  have hmem := hle (mem_readTwice_disagree ℓ μ ν)
  obtain ⟨x, u, v, -, hv, -⟩ := (Brookes.mem_bind_iff _ _ _ (μ ℓ, ν ℓ)).1 hmem
  obtain ⟨heq, -⟩ := (Brookes.mem_pure_iff (x, x) (μ ℓ, ν ℓ) v).1 hv
  exact h ((congrArg Prod.fst heq).trans (congrArg Prod.snd heq).symm)

/-! ## Separation from the trivial computation -/

/-- Reads and writes are not `pure`: every one of their traces is nonempty. -/
example (ℓ : Loc) (v : Val) : read ℓ ≠ (pure v : Comp Loc Val Val) := read_ne_pure ℓ v

example [DecidableEq Loc] (ℓ : Loc) (v : Val) :
    write ℓ v ≠ (pure PUnit.unit : Comp Loc Val PUnit) := write_ne_pure ℓ v

/-! ## Looping in the sequentially consistent model -/

theorem approx_write_forever [DecidableEq Loc] {A B : Type u} (ℓ : Loc) (v : Val) :
    ∀ (n : Nat) (a : A), Brookes.approx
      (fun a : A ↦ (write ℓ v >>= fun _ ↦ pure (Sum.inr a) : Comp Loc Val (B ⊕ A))) n a
      = (⊥ : Comp Loc Val B) := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    rw [Brookes.approx_succ, bind_assoc]
    simp only [Brookes.pure_bind_eq, Sum.elim_inr, ih, Brookes.bind_bot]

/-- A loop body that writes once and recurses forever denotes `⊥`: the productive
infinite execution is discarded. -/
theorem iter_write_forever [DecidableEq Loc] {A B : Type u} (ℓ : Loc) (v : Val) (a : A) :
    iter (fun a : A ↦ (write ℓ v >>= fun _ ↦ pure (Sum.inr a) : Comp Loc Val (B ⊕ A))) a
      = (⊥ : Comp Loc Val B) :=
  le_antisymm (Brookes.iter_le _ a fun n ↦ le_of_eq (approx_write_forever ℓ v n a)) bot_le

/-- A loop over a two-state control set: write `true`, recurse once, write
`false`, and return. -/
def loopBody : Bool → Comp PUnit Bool (PUnit ⊕ Bool)
  | true => write PUnit.unit true >>= fun _ ↦ pure (Sum.inr false)
  | false => write PUnit.unit false >>= fun _ ↦ pure (Sum.inl PUnit.unit)

/-- The loop's two-step execution: both writes appear, in order. -/
theorem mem_iter_loopBody (μ : Store PUnit Bool) :
    ([(μ, Function.update μ PUnit.unit true)] ++
      ([(Function.update μ PUnit.unit true,
          Function.update (Function.update μ PUnit.unit true) PUnit.unit false)] ++ []),
      PUnit.unit) ∈ iter loopBody true := by
  refine Brookes.mem_iter_more (a' := false) ?_ ?_
  · exact Brookes.mem_bind _ _ (mem_write PUnit.unit true μ) (Brookes.mem_pure _)
  · exact Brookes.mem_iter_done
      (Brookes.mem_bind _ _ (mem_write PUnit.unit false _) (Brookes.mem_pure _))

/-- Mumbling collapses that execution: the loop is also observed as the single
transition writing `false`. -/
theorem mem_iter_loopBody_mumbled (μ : Store PUnit Bool) :
    ([(μ, Function.update μ PUnit.unit false)], PUnit.unit) ∈ iter loopBody true := by
  refine Brookes.mem_of_refines (mem_iter_loopBody μ) ?_
  rw [← Function.update_idem true false μ]
  exact Relation.ReflTransGen.single (Step.mumble _ _ _ [])

/-! ## Mumbling is a genuine quotient -/

variable {S : Type u}

/-- Mumbling is not reversible: a merged transition does not refine back to the
two transitions it came from. -/
theorem not_refines_split {μ ρ θ : S} (hμρ : μ ≠ ρ) (hρθ : ρ ≠ θ) :
    ¬ (rewriting S).Refines [(μ, θ)] [(μ, ρ), (ρ, θ)] := by
  intro h
  have hcompat := refines_compat (r := Relation.ReflTransGen (fun x y ↦ x = μ ∧ y = θ))
    (fun _ ↦ .refl) (fun _ _ _ h₁ h₂ ↦ h₁.trans h₂) h
    (by rintro p hp; rcases List.mem_cons.1 hp with rfl | hp
        · exact .single ⟨rfl, rfl⟩
        · simp at hp)
  have hμρ' := hcompat (μ, ρ) (by simp)
  cases hμρ' with
  | refl => exact hμρ rfl
  | tail _ hstep => exact hρθ hstep.2

/-- The Brookes denotation of a two-step observation strictly contains the
denotation of its mumbled contraction: `ofFiniteTrace` is not order-reflecting,
so the Brookes model validates equations the deterministic model does not. -/
theorem ofFiniteTrace_mumble_le {A : Type u} {μ ρ θ : S} (a : A) :
    ofFiniteTrace (rewriting S) (FiniteTrace.done [(μ, θ)] a)
      ≤ ofFiniteTrace (rewriting S) (FiniteTrace.done [(μ, ρ), (ρ, θ)] a) :=
  ofFiniteTrace_le_of_refines _ (Relation.ReflTransGen.single (Step.mumble μ ρ θ [])) a

theorem ofFiniteTrace_mumble_ne {A : Type u} {μ ρ θ : S} (hμρ : μ ≠ ρ) (hρθ : ρ ≠ θ) (a : A) :
    ofFiniteTrace (rewriting S) (FiniteTrace.done [(μ, θ)] a)
      ≠ ofFiniteTrace (rewriting S) (FiniteTrace.done [(μ, ρ), (ρ, θ)] a) := by
  intro heq
  have hmem : ([(μ, ρ), (ρ, θ)], a) ∈
      ofFiniteTrace (rewriting S) (FiniteTrace.done [(μ, ρ), (ρ, θ)] a) :=
    (mem_ofFiniteTrace_iff _ _ _ _).2 ⟨[(μ, ρ), (ρ, θ)], _root_.Part.mem_some _, .refl⟩
  rw [← heq] at hmem
  obtain ⟨t₀, ht₀, hr⟩ := (mem_ofFiniteTrace_iff _ _ _ _).1 hmem
  have ht₀' : (a, t₀) = (a, [(μ, θ)]) := _root_.Part.mem_some_iff.1 ht₀
  have : t₀ = [(μ, θ)] := congrArg Prod.snd ht₀'
  subst this
  exact not_refines_split hμρ hρθ hr

end SeqCst

end Brookes

end Isotope.Elgot
