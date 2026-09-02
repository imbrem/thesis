import Isotope.Elgot.RA.Opt.Basic
import Isotope.Elgot.RA.Assoc

/-!
# Sequential program transformations, sound in the release/acquire model

Transformations of Fig. 3 (journal p.12) and Table 3 (journal p.44) of Dvir,
Kammar and Lahav (`release-acquire`, TOPLAS 47(2):7), proved here as refinements
between `Comp R Loc Val` computations built from `store`, `rmw`, `load` and
`>>=`.

## Scope, stated precisely

These are theorems about the **denotational model**, quantified over all
locations, values and (where stated) all rule sets in a named range.  They are
*not* theorems about a syntax: the repository's `λ`-iter has no memory
instructions and no parallel composition, and its equational judgment is a
symmetric equality whereas every transformation here is directed.  Nothing below
should be described as "sound for `λ`-iter"; see the honest boundary in
`Isotope/Elgot/RA/Opt.lean`.

Compositionality is available separately and is what lets these be used inside
larger programs: `Comp.bind_mono`, `Comp.par_mono` and `Comp.iterate_mono`
together say refinement is a precongruence for the model's constructs.  That is
a statement about the model, not the paper's adequacy theorem, which is not
formalized here.

## Direction

`P ≤ Q` is `P.traces ⊆ Q.traces` and validates the paper's `Q ↠ P`.

## Contents

| here | paper | rule |
|---|---|---|
| `pure_le_load_bind` | Prop. E.3, Irrelevant Read Elimination (p.59) | `Mu` |
| `load_bind_le_pure` | Prop. E.2, Irrelevant Read Introduction (p.58) | `St`, `Fw` |
| `load_bind_pure_eq`, `load_bind_eq` | *stronger than* both: an equality | — |
| `store_pure_le_store_load` | Prop. E.9, the `ℓ:=v ; ℓ? ↠ ℓ:=v ; v` instance:
  the Table 3 row carrying **no** `𝔞`-rule | `Mu` |
| `xchg_le_store` | Prop. E.4, Atomic Store (p.58) | — |
| `iterate_load_body` | not in the paper (it has no loops) | — |
-/

namespace Isotope.Elgot.RA

-- Everything here mixes the result type with `Val` through `>>=`, so the result
-- types live in the same universe as `Val`, namely `Type`.
variable {Loc Val : Type} {R : RuleSet} {A B : Type} [DecidableEq Loc]

/-! ## Loads, at the level of generators -/

/-- A stutter over a well-formed memory that a view points downwards into is a
generating trace of `⟦load ℓ⟧`, returning the value of the message the view
points at.  This is the "the load is free" step of the paper's proof of
Prop. E.3: the trace conditions on a `return`-trace already exhibit the message
the load reads. -/
theorem mem_loadGen (ℓ : Loc) {κ : View Loc} {μ : Memory Loc Val} (hwf : WellFormed μ)
    (hpd : PointsDownInto κ μ) :
    ∃ ν ∈ μ, ν.lc = ℓ ∧
      (⟨κ, Chro.single ⟨μ, μ⟩, κ, ν.vl⟩ : PreTrace Loc Val Val)
        ∈ (load (R := R) ℓ : Comp R Loc Val Val).traces := by
  obtain ⟨ν, hν, hlc, hpt, -⟩ := hpd ℓ
  refine ⟨ν, hν, hlc, subset_closure (Or.inl ⟨κ, μ, ν, hν, hlc, hpt, rfl, rfl, ?_⟩)⟩
  exact pureGen_isTrace ν.vl _ ⟨κ, μ, hwf, hpd, rfl⟩

omit [DecidableEq Loc] in
/-- Every generating trace of `⟦load ℓ⟧` has no local messages: a load adds
nothing to memory. -/
theorem rmwROGen_own (ℓ : Loc) (Φ : Val → Option Val) {τ : PreTrace Loc Val Val}
    (h : τ ∈ rmwROGen ℓ Φ) : τ.ch.own = ∅ := by
  obtain ⟨κ, μ, ν, -, -, -, -, rfl, -⟩ := h
  simp [Transition.own]

/-- …and so does every trace of `⟦load ℓ⟧`, for every rule set below
`𝔤𝔠 ∪ {Ti, Ab}`. -/
theorem load_own (hRg : R ⊆ gcTiAbRules) (ℓ : Loc) {τ : PreTrace Loc Val Val}
    (h : τ ∈ (load ℓ : Comp R Loc Val Val).traces) : τ.ch.own = ∅ := by
  rw [load_eq, Comp.traces_close] at h
  obtain ⟨τ₀, hτ₀, hr⟩ := h
  exact hr.own_empty hRg (rmwROGen_own ℓ _ hτ₀)

/-! ## Irrelevant Read Elimination and Introduction -/

/-- **Irrelevant Read Elimination**, the paper's Proposition E.3 (journal p.59):
`ℓ? ; ⟨⟩ ↠ ⟨⟩`, i.e. `⟦ℓ? ; ⟨⟩⟧ ⊇ ⟦⟨⟩⟧`.  Needs `Mu` only, and holds at every
rule set containing it.

The proof is the paper's: the well-formedness of a `return`-trace already
supplies a message at `ℓ` that the initial view points at, so the load is
obtained for free over the same stutter, and one `Mumble` merges the two
transitions. -/
theorem pure_le_load_bind (hMu : Rule.Mu ∈ R) (ℓ : Loc) (r : A) :
    (Pure.pure r : Comp R Loc Val A) ≤ (load ℓ >>= fun _ ↦ Pure.pure r) := by
  rw [Comp.le_def, Comp.traces_pure]
  refine closure_subset_of_closed (Comp.closed _) ?_
  rintro τ₀ ⟨κ, μ, hwf, hpd, rfl⟩
  obtain ⟨ν, hν, hlc, hload⟩ := mem_loadGen (R := R) ℓ hwf hpd
  set ld : PreTrace Loc Val Val := ⟨κ, Chro.single ⟨μ, μ⟩, κ, ν.vl⟩ with hlddef
  set υ : PreTrace Loc Val A := ⟨κ, Chro.single ⟨μ, μ⟩, κ, r⟩ with hυdef
  have hυg : υ ∈ pureGen (Loc := Loc) (Val := Val) r := ⟨κ, μ, hwf, hpd, rfl⟩
  have hseam : ld.ch.c ⊆ υ.ch.o := by rw [hlddef, hυdef]; simp
  have hmem : ld.seam υ hseam
      ∈ (load ℓ >>= fun _ ↦ (Pure.pure r : Comp R Loc Val A)).traces :=
    subset_closure ⟨ld, υ, hseam, hload, subset_closure hυg, le_refl _, rfl⟩
  refine (Comp.closed _).mem_of_refines hmem (Refines.single ⟨?_, ?_⟩)
  · exact Step.chro hMu (ChroStep.mumble _ _ [] [] μ μ μ rfl rfl)
  · exact pureGen_isTrace r _ hυg

/-- **Irrelevant Read Introduction**, the paper's Proposition E.2 (journal
p.58): `⟨⟩ ↠ ℓ? ; ⟨⟩`, i.e. `⟦⟨⟩⟧ ⊇ ⟦ℓ? ; ⟨⟩⟧`.  Needs `St` and `Fw`, and the
rule set must exclude `Dilute`, which would let the composite acquire a local
message.

Our proof is shorter than the paper's: a load contributes no local message, so
the composite has none, and `mem_pure_of_own_empty` turns that into membership
of `return` directly. -/
theorem load_bind_le_pure (hcR : cRules ⊆ R) (hRg : R ⊆ gcTiAbRules) (ℓ : Loc) (r : A) :
    (load ℓ >>= fun _ ↦ (Pure.pure r : Comp R Loc Val A)) ≤ Pure.pure r := by
  rw [Comp.le_def, Comp.traces_bind_pure_comp (B := A) hcR hRg (load ℓ) (fun _ ↦ r)]
  refine closure_subset_of_closed (Comp.closed _) ?_
  rintro π ⟨τ, hτ, rfl⟩
  have hown : (τ.mapRet (fun _ ↦ r)).ch.own = ∅ := load_own hRg ℓ hτ
  exact mem_pure_of_own_empty (hcR (by simp)) (hcR (by simp))
    ((load ℓ : Comp R Loc Val Val).isTrace _ hτ).mapRet hown

/-- **An irrelevant load is denotationally invisible in the Concrete model
`C`.**  This is an *equality*, strictly stronger than the paper's two
one-directional propositions E.2 and E.3, which it packages together. -/
theorem load_bind_pure_eq (ℓ : Loc) (r : A) :
    (load ℓ >>= fun _ ↦ (Pure.pure r : Comp gcRules Loc Val A)) = Pure.pure r :=
  le_antisymm
    (load_bind_le_pure cRules_subset_gcRules gcRules_subset_gcTiAbRules ℓ r)
    (pure_le_load_bind (by simp) ℓ r)

/-- **A load may be deleted from in front of any computation** of the Concrete
model.  The paper states the special case `x? ; y? ↠ y?` as a remark (journal
p.10) and derives it from E.2/E.3; the general form here follows from
`load_bind_pure_eq` and associativity, both of which are available at `𝔤𝔠`. -/
theorem load_bind_eq (ℓ : Loc) (P : Comp gcRules Loc Val A) :
    (load ℓ >>= fun _ ↦ P) = P := by
  have h : (load ℓ >>= fun _ ↦ P)
      = (load ℓ >>= fun _ ↦ (Pure.pure () : Comp gcRules Loc Val Unit)) >>= fun _ ↦ P := by
    rw [bind_assoc]
    simp only [pure_bind]
  rw [h, load_bind_pure_eq, pure_bind]

/-- The paper's own remark at journal p.10: `x? ; y? ↠ y?`, here as an
equality. -/
theorem load_bind_load_eq (ℓ ℓ' : Loc) :
    (load ℓ >>= fun _ ↦ (load ℓ' : Comp gcRules Loc Val Val)) = load ℓ' :=
  load_bind_eq ℓ (load ℓ')

/-! ## Reading back your own write -/

/-- **Write-Read Elimination**: `ℓ:=v ; ℓ? ↠ ℓ:=v ; v`, i.e.
`⟦ℓ:=v ; ℓ?⟧ ⊇ ⟦ℓ:=v ; v⟧`.  This is the ground instance of the paper's
Proposition E.9 (journal p.60) in which the modifier is undefined on the stored
value, and it is the Table 3 row (p.44) that carries **no** `𝔞`-rule label — the
transformation transfers to the release/acquire *concrete* model verbatim.
Contrast `Isotope/Elgot/Opt/WriteWrite.lean`.

Proof: the store's final view `κ[ℓ↦t]` points at exactly the message it wrote,
so a load over the store's closing memory is forced to return `v`; one `Mumble`
merges the two transitions, and the rewriting of an arbitrary trace of the store
is carried along by `Refines.mapRet`. -/
theorem store_pure_le_store_load (hcR : cRules ⊆ R) (hRg : R ⊆ gcTiAbRules)
    (ℓ : Loc) (v : Val) :
    (store ℓ v >>= fun _ ↦ (Pure.pure v : Comp R Loc Val Val))
      ≤ (store ℓ v >>= fun _ ↦ load ℓ) := by
  rw [Comp.le_def, Comp.traces_bind_pure_comp hcR hRg (store ℓ v) (fun _ ↦ v)]
  refine closure_subset_of_closed (Comp.closed _) ?_
  rintro π ⟨τ, ⟨τ₀, hτ₀, hr⟩, rfl⟩
  refine (Comp.closed _).mem_of_refines (?_ : τ₀.mapRet (fun _ ↦ v) ∈ _)
    (hr.mapRet (fun _ ↦ v))
  obtain ⟨κ, μ, q, t, hqt, rfl, hτ₀'⟩ := hτ₀
  set w : Msg Loc Val := writeMsg ℓ v q t κ hqt with hwdef
  set ρ : Memory Loc Val := insert w μ with hρdef
  have hwfρ : WellFormed ρ := hτ₀'.wf_c
  have hpdρ : PointsDownInto (setView κ ℓ t) ρ := hτ₀'.closePts
  set ld : PreTrace Loc Val Val :=
    ⟨setView κ ℓ t, Chro.single ⟨ρ, ρ⟩, setView κ ℓ t, v⟩ with hlddef
  have hldt : IsTrace ld :=
    pureGen_isTrace v _ ⟨setView κ ℓ t, ρ, hwfρ, hpdρ, rfl⟩
  have hload : ld ∈ (load ℓ : Comp R Loc Val Val).traces := by
    refine subset_closure (Or.inl ⟨setView κ ℓ t, ρ, w, Set.mem_insert _ _, rfl, ?_, rfl,
      rfl, hldt⟩)
    change setView κ ℓ t w.lc = w.t
    simp [hwdef]
  have hseam : (⟨κ, Chro.single ⟨μ, ρ⟩, setView κ ℓ t, ()⟩ :
      PreTrace Loc Val Unit).ch.c ⊆ ld.ch.o := by simp [hlddef]
  have hmem : (⟨κ, Chro.single ⟨μ, ρ⟩, setView κ ℓ t, ()⟩ :
        PreTrace Loc Val Unit).seam ld hseam
      ∈ (store ℓ v >>= fun _ ↦ (load ℓ : Comp R Loc Val Val)).traces :=
    subset_closure ⟨_, ld, hseam, subset_closure ⟨κ, μ, q, t, hqt, rfl, hτ₀'⟩,
      hload, le_refl _, rfl⟩
  refine (Comp.closed _).mem_of_refines hmem (Refines.single ⟨?_, hτ₀'.mapRet⟩)
  exact Step.chro (hcR (by simp)) (ChroStep.mumble _ _ [] [] μ ρ ρ rfl rfl)

/-! ## Atomic Store -/

/-- **Atomic Store**, the paper's Proposition E.4 (journal p.58):
`ℓ:=v ↠ XCHG(ℓ,v) ; ⟨⟩`, i.e. `⟦ℓ:=v⟧ ⊇ ⟦XCHG(ℓ,v) ; ⟨⟩⟧`.  An exchange writing
`v` unconditionally, with its return value discarded, refines a plain store.

The paper's proof is the one line "take the traces in `⟦ℓ:=v⟧_G` in which the
newly added message dovetails after the previous message in memory by choosing
the initial timestamp appropriately"; here that is the instantiation
`q := ν.t`.  The read-only branch of the exchange is empty because its modifier
is everywhere defined. -/
theorem xchg_le_store (hcR : cRules ⊆ R) (hRg : R ⊆ gcTiAbRules) (ℓ : Loc) (v : Val) :
    (rmw ℓ (fun _ ↦ some v) >>= fun _ ↦ (Pure.pure () : Comp R Loc Val Unit))
      ≤ store ℓ v := by
  rw [Comp.le_def,
    Comp.traces_bind_pure_comp hcR hRg (rmw ℓ (fun _ ↦ some v)) (fun _ ↦ ())]
  refine closure_subset_of_closed (Comp.closed _) ?_
  rintro π ⟨τ, ⟨τ₀, hτ₀, hr⟩, rfl⟩
  refine (Comp.closed _).mem_of_refines (?_ : τ₀.mapRet (fun _ ↦ ()) ∈ _)
    (hr.mapRet (fun _ ↦ ()))
  rcases hτ₀ with ⟨κ, μ, ν, -, -, -, hΦ, -⟩ | ⟨κ, μ, ν, w, t, hνt, -, -, -, hΦ, rfl, hτ₀'⟩
  · exact absurd hΦ (by simp)
  · have hwv : w = v := by simpa using hΦ.symm
    subst hwv
    exact subset_closure ⟨κ, μ, ν.t, t, hνt, rfl, hτ₀'.mapRet⟩

/-! ## Loops

The paper has no iteration operator (journal §4), so everything in this section
is ours. -/

/-- **An irrelevant load may be hoisted out of a loop body.**  Immediate from
`load_bind_eq`, but it is the first place where a transformation of the model is
carried through the iteration operator. -/
theorem iterate_load_body (ℓ : Loc) (f : A → Comp gcRules Loc Val (B ⊕ A)) :
    Comp.iterate (fun a ↦ load ℓ >>= fun _ ↦ f a) = Comp.iterate f :=
  Comp.iterate_congr (fun a ↦ load_bind_eq ℓ (f a))

end Isotope.Elgot.RA
