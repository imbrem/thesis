import Isotope.Elgot.Brookes.SeqCst.Chunk

/-!
# The shared-variable parallel language and its trace semantics

Brookes's language (journal §2):

```
C ::= skip | I := E | C₁ ; C₂ | C₁ ∥ C₂
    | if B then C₁ else C₂ | while B do C | await B then C
```

and his trace semantics, **transcribed** from Proposition 6.2 (journal p. 150):

```
T[skip]                 = {(s,s) | s ∈ S}†
T[I:=E]                 = {(s,[s | I = n]) | (s,n) ∈ E[E]}†
T[C₁;C₂]                = T[C₁] ; T[C₂]
T[C₁ ∥ C₂]              = T[C₁] ∥ T[C₂]
T[if B then C₁ else C₂] = T[B];T[C₁] ∪ T[¬B];T[C₂]
T[while B do C]         = (T[B];T[C])* ; T[¬B]
T[await B then C]       = {(s,s') ∈ T[C] | (s,tt) ∈ B[B]}†
```

Brookes takes these clauses to *characterise* the operationally defined `T`
(that is his Proposition 6.2).  **We take them as the definition**: no
operational semantics is formalized here, and Proposition 6.2 is therefore not
formalized either.  Everything downstream — the observation, the contextual
preorder, soundness and full abstraction — is about this denotational `T`, which
is a faithful reading of §6–§7 but leaves that one bridge unformalized.  See the
honest boundary in `Isotope/Elgot/Brookes/SeqCst/FullAbstraction.lean`.

## Deviations from the paper, and why

* **States are total.**  Brookes uses finite partial maps and carries
  `free[C] ∪ free[C'] ⊆ dom(s)` side conditions everywhere.  We use
  `Store Loc Val = Loc → Val` with `Loc` finite, which removes the side
  conditions and keeps `IS_s` and `MAKE_s` (needed for definability) definable.
* **Expressions are constants and variables.**  Brookes allows arbitrary
  arithmetic; since `Val` is an arbitrary type here there are no operations to
  offer, and expression structure plays no role in the full-abstraction argument
  (with atomic evaluation his `E` and `B` are already fully abstract for their
  sub-languages, journal p. 151).  Boolean expressions are exactly the finite
  conjunctions of equations that his condition language is assumed to contain
  (journal p. 148), closed under negation.
* **Denotations are `ε`-free.**  Brookes's traces are non-empty (`P†(Σ⁺)`); the
  Brookes *monad* of this repository admits the empty trace, because `pure` is
  its closure.  `den` is arranged so that every command denotation omits `ε`
  (`nil_not_mem_den`) — `skip` denotes `T[true]`, not `pure`.  This matters:
  with `ε ∈ T[skip]` but `ε ∉ T[true];T[skip]`, `skip` and
  `if true then skip else skip` would be contextually equal yet denotationally
  different, and full abstraction would be false.
* **`await` bodies are unrestricted commands.**  Brookes restricts them
  syntactically to finite sequences of assignments; we allow any command and
  keep his clause verbatim.  The restriction is only needed to justify atomicity
  operationally, which we do not formalize.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {Loc Val : Type u}

/-! ## Atomic computations, the observation, and derived operations -/

/-- The atomic computation performing one state transition satisfying `R`.
This is the closure of a set of one-pair traces, and covers all of the paper's
primitives: `skip`, assignment, boolean tests, and conditional critical
regions. -/
def atom (R : Store Loc Val → Store Loc Val → Prop) : Comp Loc Val PUnit :=
  close _ {q | ∃ μ ν, R μ ν ∧ q.1 = [(μ, ν)]}

theorem mem_atom_iff {R : Store Loc Val → Store Loc Val → Prop}
    {t : Trace (Store Loc Val × Store Loc Val)} {x : PUnit} :
    (t, x) ∈ atom R ↔ ∃ μ ν, R μ ν ∧ (rewriting _).Refines [(μ, ν)] t := by
  constructor
  · rintro ⟨t₀, ⟨μ, ν, hR, rfl⟩, hr⟩; exact ⟨μ, ν, hR, hr⟩
  · rintro ⟨μ, ν, hR, hr⟩; exact ⟨_, ⟨μ, ν, hR, rfl⟩, hr⟩

/-- **Brookes's `M`** (Definition 4.1), extracted from the trace semantics as he
does in journal §6: `M[C] = {(s,s') | (s,s') ∈ T[C]}`, the one-pair traces. -/
def obs (x : Comp Loc Val PUnit) (μ ν : Store Loc Val) : Prop :=
  ([(μ, ν)], PUnit.unit) ∈ x

theorem obs_mono {x y : Comp Loc Val PUnit} (h : x ≤ y) {μ ν : Store Loc Val}
    (hm : obs x μ ν) : obs y μ ν := h hm

/-- The observation of an atomic computation is exactly its relation. -/
@[simp] theorem obs_atom {R : Store Loc Val → Store Loc Val → Prop}
    {μ ν : Store Loc Val} : obs (atom R) μ ν ↔ R μ ν := by
  constructor
  · intro h
    obtain ⟨μ₀, ν₀, hR, hr⟩ := mem_atom_iff.1 h
    obtain ⟨rfl, hc⟩ := (chain_iff_refines_single.2 hr).cons_inv rfl
    obtain rfl := hc.nil_inv
    exact hR
  · intro h; exact mem_atom_iff.2 ⟨μ, ν, h, .refl⟩

theorem atom_mono {R R' : Store Loc Val → Store Loc Val → Prop}
    (h : ∀ μ ν, R μ ν → R' μ ν) : atom R ≤ atom R' := by
  apply le_of_mem
  intro t x hm
  obtain ⟨μ, ν, hR, hr⟩ := mem_atom_iff.1 hm
  exact mem_atom_iff.2 ⟨μ, ν, h μ ν hR, hr⟩

/-- **Brookes's `M[C₁;C₂] = M[C₁];M[C₂]`**: the observation is a monad morphism
into the relations.  This is the one-pair fragment of `T[C₁;C₂] = T[C₁];T[C₂]`
and needs `Chain.split`. -/
theorem obs_bind {x : Comp Loc Val PUnit} {f : PUnit → Comp Loc Val PUnit}
    {μ ν : Store Loc Val} :
    obs (x >>= f) μ ν ↔ ∃ ρ, obs x μ ρ ∧ obs (f PUnit.unit) ρ ν := by
  constructor
  · intro h
    obtain ⟨a, u, v, hu, hv, hr⟩ := (mem_bind_iff _ _ _ _).1 h
    obtain ⟨ρ, h₁, h₂⟩ := (chain_iff_refines_single.2 hr).split
    obtain rfl : a = PUnit.unit := rfl
    exact ⟨ρ, mem_of_refines hu h₁.refines_single, mem_of_refines hv h₂.refines_single⟩
  · rintro ⟨ρ, h₁, h₂⟩
    refine mem_of_refines (mem_bind x f h₁ h₂) ?_
    exact .single (Step.mumble μ ρ ν [])

/-- The test computation: `T[B] = {(s,s) | (s,tt) ∈ B[B]}†` (journal p. 150). -/
def test (p : Store Loc Val → Bool) : Comp Loc Val PUnit :=
  atom fun μ ν ↦ p μ = true ∧ ν = μ

@[simp] theorem obs_test {p : Store Loc Val → Bool} {μ ν : Store Loc Val} :
    obs (test p) μ ν ↔ p μ = true ∧ ν = μ := obs_atom

/-- Binary union of computations; closed sets are stable under unions, so no
closure step is needed. -/
def union2 (x y : Comp Loc Val PUnit) : Comp Loc Val PUnit :=
  Brookes.iUnion fun b : Bool ↦ cond b x y

@[simp] theorem mem_union2_iff {x y : Comp Loc Val PUnit}
    {p : Trace (Store Loc Val × Store Loc Val) × PUnit} :
    p ∈ union2 x y ↔ p ∈ x ∨ p ∈ y := by
  rw [union2, Brookes.mem_iUnion_iff]
  constructor
  · rintro ⟨b, hb⟩; cases b
    · exact Or.inr hb
    · exact Or.inl hb
  · rintro (h | h)
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩

theorem union2_mono {x x' y y' : Comp Loc Val PUnit} (hx : x ≤ x') (hy : y ≤ y') :
    union2 x y ≤ union2 x' y' := by
  apply le_of_mem
  intro t a hm
  rcases mem_union2_iff.1 hm with h | h
  · exact mem_union2_iff.2 (Or.inl (hx h))
  · exact mem_union2_iff.2 (Or.inr (hy h))

/-- The `n`-fold sequential power of a computation. -/
def power (x : Comp Loc Val PUnit) : Nat → Comp Loc Val PUnit
  | 0 => pure PUnit.unit
  | n + 1 => x >>= fun _ ↦ power x n

/-- Kleene star: `T* = ⋃ₙ Tⁿ`, the paper's least set containing `T` and `ε` and
closed under stuttering, mumbling and concatenation. -/
def star (x : Comp Loc Val PUnit) : Comp Loc Val PUnit :=
  Brookes.iUnion (power x)

theorem power_mono {x y : Comp Loc Val PUnit} (h : x ≤ y) (n : Nat) :
    power x n ≤ power y n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => exact bind_mono h fun _ ↦ ih

theorem star_mono {x y : Comp Loc Val PUnit} (h : x ≤ y) : star x ≤ star y :=
  Brookes.iUnion_le fun n ↦ (power_mono h n).trans (Brookes.le_iUnion _ n)

/-! ## Syntax -/

/-- Expressions: constants and identifiers.  Brookes allows arbitrary
arithmetic; `Val` here is an arbitrary type, so there are no operations. -/
inductive Exp (Loc Val : Type u) : Type u
  | /-- A constant. -/ const (v : Val)
  | /-- An identifier. -/ var (ℓ : Loc)

/-- Boolean expressions: the finite conjunctions of equations that Brookes's
condition language is assumed to contain (journal p. 148), closed under
negation. -/
inductive BExp (Loc Val : Type u) : Type u
  | /-- Truth. -/ tt
  | /-- Falsity. -/ ff
  | /-- An equation between expressions. -/ eq (e₁ e₂ : Exp Loc Val)
  | /-- Conjunction. -/ and (b₁ b₂ : BExp Loc Val)
  | /-- Negation. -/ neg (b : BExp Loc Val)

/-- Brookes's command syntax (journal §2). -/
inductive Com (Loc Val : Type u) : Type u
  | /-- `skip`. -/ skip
  | /-- `I := E`. -/ assign (ℓ : Loc) (e : Exp Loc Val)
  | /-- `C₁ ; C₂`. -/ seq (C₁ C₂ : Com Loc Val)
  | /-- `C₁ ∥ C₂`. -/ par (C₁ C₂ : Com Loc Val)
  | /-- `if B then C₁ else C₂`. -/ ite (b : BExp Loc Val) (C₁ C₂ : Com Loc Val)
  | /-- `while B do C`. -/ wh (b : BExp Loc Val) (C : Com Loc Val)
  | /-- `await B then C`, a conditional critical region. -/
    await (b : BExp Loc Val) (C : Com Loc Val)

/-- Expression evaluation. -/
def Exp.eval : Exp Loc Val → Store Loc Val → Val
  | .const v, _ => v
  | .var ℓ, μ => μ ℓ

/-- Boolean expression evaluation. -/
def BExp.eval [DecidableEq Val] : BExp Loc Val → Store Loc Val → Bool
  | .tt, _ => true
  | .ff, _ => false
  | .eq e₁ e₂, μ => decide (e₁.eval μ = e₂.eval μ)
  | .and b₁ b₂, μ => b₁.eval μ && b₂.eval μ
  | .neg b, μ => !b.eval μ

/-! ## The trace semantics -/

/-- **The trace semantics `T`**, transcribed from Brookes's Proposition 6.2. -/
def den [DecidableEq Loc] [DecidableEq Val] : Com Loc Val → Comp Loc Val PUnit
  | .skip => test fun _ ↦ true
  | .assign ℓ e => atom fun μ ν ↦ ν = Function.update μ ℓ (e.eval μ)
  | .seq C₁ C₂ => den C₁ >>= fun _ ↦ den C₂
  | .par C₁ C₂ => (fun _ ↦ PUnit.unit) <$> Brookes.par (den C₁) (den C₂)
  | .ite b C₁ C₂ =>
      union2 (test b.eval >>= fun _ ↦ den C₁) (test (BExp.neg b).eval >>= fun _ ↦ den C₂)
  | .wh b C => star (test b.eval >>= fun _ ↦ den C) >>= fun _ ↦ test (BExp.neg b).eval
  | .await b C => atom fun μ ν ↦ b.eval μ = true ∧ obs (den C) μ ν

section Equations

variable [DecidableEq Loc] [DecidableEq Val]

@[simp] theorem den_skip : den (Com.skip : Com Loc Val) = test fun _ ↦ true := by rw [den]

@[simp] theorem den_assign (ℓ : Loc) (e : Exp Loc Val) :
    den (Com.assign ℓ e) = atom fun μ ν ↦ ν = Function.update μ ℓ (e.eval μ) := by rw [den]

@[simp] theorem den_seq (C₁ C₂ : Com Loc Val) :
    den (Com.seq C₁ C₂) = (den C₁ >>= fun _ ↦ den C₂) := by rw [den]

@[simp] theorem den_par (C₁ C₂ : Com Loc Val) :
    den (Com.par C₁ C₂) = (fun _ ↦ PUnit.unit) <$> Brookes.par (den C₁) (den C₂) := by rw [den]

@[simp] theorem den_ite (b : BExp Loc Val) (C₁ C₂ : Com Loc Val) :
    den (Com.ite b C₁ C₂) =
      union2 (test b.eval >>= fun _ ↦ den C₁) (test (BExp.neg b).eval >>= fun _ ↦ den C₂) := by
  rw [den]

@[simp] theorem den_wh (b : BExp Loc Val) (C : Com Loc Val) :
    den (Com.wh b C) =
      (star (test b.eval >>= fun _ ↦ den C) >>= fun _ ↦ test (BExp.neg b).eval) := by rw [den]

@[simp] theorem den_await (b : BExp Loc Val) (C : Com Loc Val) :
    den (Com.await b C) = atom fun μ ν ↦ b.eval μ = true ∧ obs (den C) μ ν := by rw [den]

end Equations

/-- **Brookes's observation** `M[C]` of a command. -/
def Obs [DecidableEq Loc] [DecidableEq Val] (C : Com Loc Val)
    (μ ν : Store Loc Val) : Prop := obs (den C) μ ν

/-! ## Every command denotation is `ε`-free -/

theorem nil_not_mem_atom {R : Store Loc Val → Store Loc Val → Prop} (x : PUnit) :
    (([] : Trace (Store Loc Val × Store Loc Val)), x) ∉ atom R := by
  intro h
  obtain ⟨μ, ν, _, hr⟩ := mem_atom_iff.1 h
  exact absurd (refines_nil hr) (by simp)

theorem nil_not_mem_bind {x : Comp Loc Val PUnit} {f : PUnit → Comp Loc Val PUnit}
    (hx : (([] : Trace (Store Loc Val × Store Loc Val)), PUnit.unit) ∉ x) (a : PUnit) :
    (([] : Trace (Store Loc Val × Store Loc Val)), a) ∉ (x >>= f) := by
  intro h
  obtain ⟨b, u, v, hu, _, hr⟩ := (mem_bind_iff _ _ _ _).1 h
  obtain hnil := refines_nil hr
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hnil
  exact hx hu

theorem nil_not_mem_bind_right {x : Comp Loc Val PUnit} {f : PUnit → Comp Loc Val PUnit}
    (hf : ∀ b, (([] : Trace (Store Loc Val × Store Loc Val)), PUnit.unit) ∉ f b) (a : PUnit) :
    (([] : Trace (Store Loc Val × Store Loc Val)), a) ∉ (x >>= f) := by
  intro h
  obtain ⟨b, u, v, _, hv, hr⟩ := (mem_bind_iff _ _ _ _).1 h
  obtain hnil := refines_nil hr
  obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.1 hnil
  exact hf b hv

theorem nil_not_mem_par {x y : Comp Loc Val PUnit}
    (hx : (([] : Trace (Store Loc Val × Store Loc Val)), PUnit.unit) ∉ x) (a : PUnit) :
    (([] : Trace (Store Loc Val × Store Loc Val)), a) ∉
      ((fun _ ↦ PUnit.unit) <$> Brookes.par x y) := by
  intro h
  obtain ⟨p, _, hp⟩ := mem_map_iff.1 h
  obtain ⟨w₀, t, u, ht, _, hi, hr⟩ := mem_par_iff'.1 hp
  obtain rfl := refines_nil hr
  cases hi
  exact hx ht

/-- **Every command denotation omits the empty trace.**  Brookes's traces are
non-empty; this is where that is recovered, and it is what makes full
abstraction true for the monadic presentation. -/
theorem nil_not_mem_den [DecidableEq Loc] [DecidableEq Val] (C : Com Loc Val) (a : PUnit) :
    (([] : Trace (Store Loc Val × Store Loc Val)), a) ∉ den C := by
  induction C with
  | skip => exact nil_not_mem_atom a
  | assign ℓ e => exact nil_not_mem_atom a
  | seq C₁ C₂ ih₁ _ => exact nil_not_mem_bind ih₁ a
  | par C₁ C₂ ih₁ _ => exact nil_not_mem_par ih₁ a
  | ite b C₁ C₂ _ _ =>
      intro h
      rcases mem_union2_iff.1 h with h | h
      · exact nil_not_mem_bind (nil_not_mem_atom PUnit.unit) a h
      · exact nil_not_mem_bind (nil_not_mem_atom PUnit.unit) a h
  | wh b C _ => exact nil_not_mem_bind_right (fun _ ↦ nil_not_mem_atom PUnit.unit) a
  | await b C _ => exact nil_not_mem_atom a

end SeqCst

end Isotope.Elgot.Brookes
