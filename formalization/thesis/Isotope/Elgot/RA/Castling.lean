import Isotope.Elgot.RA.GTrace
import Isotope.Elgot.RA.Closure

/-!
# Rewrite Castling

Dvir, Kammar and Lahav's **Lemma 8.3** (journal §8.1, p.39; called *Rewrite
Commutativity* in the paper's own §3 summary, p.11):

> We write `x ⇄ y` when `(─x→ ; ─y→) ⊆ (─y→ ; ─x→)`, where the rewrites are
> restricted to traces.  **Lemma 8.3.** If `x ∈ 𝔞` and `y ∈ 𝔤𝔠`, or `x ∈ 𝔠𝔞`
> and `y ∈ 𝔤`, then `x ⇄ y`.

with the consequence the paper draws from it (p.39):

> every sequence of rewrites can be rearranged such that `𝔤`-rewrites appear
> first, then `𝔠`-rewrites, and finally `𝔞`-rewrites.

We formalize the half of Lemma 8.3 that this development can use: `x ∈ 𝔠` and
`y ∈ 𝔤`, i.e. the twelve cases of Table 5 (p.62) numbered 1–18 — `St ⇄ y` and
`Mu ⇄ y` (diagrams 1–12) and `Fw ⇄ y`, `Rw ⇄ y` (diagrams 13–18), for
`y ∈ {Ls, Ex, Cn}`.  The `𝔞` half is out of scope, the group `𝔞` not being
formalized.

The paper's proof (Appendix F, pp.61–63) runs each case through Lemma F.1, its
characterization of when the target of a rewrite is a trace.  We instead use
`Isotope/Elgot/RA/GTrace.lean`: the intermediate pre-trace produced by castling
has (almost) the same memories as the trace at the end of the given sequence,
so its transitions are well-formed for free, and the three transfer lemmas
`isTrace_loosen`, `isTrace_expel`, `isTrace_condense` do the rest.  The proofs
here are therefore ours, not a port, though the case analysis follows the
paper's.

`Castles` packages the conclusion as an interface, so that the consequences —
`Refines.sort`, `closure_eq_of_gClosed` — are proved once and hold for any rule
sets that castle.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {A : Type u}

/-! ## Splitting a rewrite over a union of rule sets -/

theorem Step.union_cases {R₁ R₂ : RuleSet} {τ π : PreTrace Loc Val A}
    (h : Step (R₁ ∪ R₂) τ π) : Step R₁ τ π ∨ Step R₂ τ π := by
  cases h with
  | chro hx hc =>
      rcases hx with hx | hx
      exacts [Or.inl (Step.chro hx hc), Or.inr (Step.chro hx hc)]
  | forward hx h =>
      rcases hx with hx | hx
      exacts [Or.inl (Step.forward hx h), Or.inr (Step.forward hx h)]
  | rewind hx h =>
      rcases hx with hx | hx
      exacts [Or.inl (Step.rewind hx h), Or.inr (Step.rewind hx h)]
  | condense hx l m ν ε hde hfν hfε h₁ h₂ =>
      rcases hx with hx | hx
      exacts [Or.inl (Step.condense hx l m ν ε hde hfν hfε h₁ h₂),
        Or.inr (Step.condense hx l m ν ε hde hfν hfε h₁ h₂)]

theorem TStep.union_cases {R₁ R₂ : RuleSet} {τ π : PreTrace Loc Val A}
    (h : TStep (R₁ ∪ R₂) τ π) : TStep R₁ τ π ∨ TStep R₂ τ π :=
  h.1.union_cases.imp (fun hs ↦ ⟨hs, h.2⟩) (fun hs ↦ ⟨hs, h.2⟩)

/-! ## The interface -/

/-- The paper's `x ⇄ y` (journal p.39), for rule *sets* and for whole rewrite
sequences on the left: an `Rc`-rewrite followed by an `Rg`-rewrite, both
restricted to traces, can be rearranged into `Rg`-rewrites followed by a single
`Rc`-rewrite. -/
def Castles (Rc Rg : RuleSet) (Loc Val : Type) : Prop :=
  ∀ {A : Type u} {τ₁ τ₂ τ₃ : PreTrace Loc Val A}, IsTrace τ₁ → TStep Rc τ₁ τ₂ →
    TStep Rg τ₂ τ₃ → ∃ τ₂', Refines Rg τ₁ τ₂' ∧ TStep Rc τ₂' τ₃

/-- Pushing a single `Rc`-rewrite past a whole sequence of `Rg`-rewrites. -/
theorem Castles.push {Rc Rg : RuleSet} (hcast : Castles.{u} Rc Rg Loc Val)
    {τ₁ τ₂ σ : PreTrace Loc Val A} (hτ₁ : IsTrace τ₁) (h : TStep Rc τ₁ τ₂)
    (hr : Refines Rg τ₂ σ) : ∃ σ', Refines Rg τ₁ σ' ∧ TStep Rc σ' σ := by
  induction hr with
  | refl => exact ⟨τ₁, Refines.refl _, h⟩
  | tail _ hstep ih =>
      obtain ⟨σ₀, hrσ, hcσ⟩ := ih
      obtain ⟨σ', hrσ', hcσ'⟩ := hcast (hrσ.isTrace hτ₁) hcσ hstep
      exact ⟨σ', hrσ.trans hrσ', hcσ'⟩

/-- **The rearrangement the paper draws from Rewrite Castling** (journal p.39):
every `Rg ∪ Rc`-rewrite sequence factors as `Rg`-rewrites followed by
`Rc`-rewrites. -/
theorem Refines.sort {Rc Rg : RuleSet} (hcast : Castles.{u} Rc Rg Loc Val)
    {τ π : PreTrace Loc Val A} (hτ : IsTrace τ) (h : Refines (Rg ∪ Rc) τ π) :
    ∃ σ, Refines Rg τ σ ∧ Refines Rc σ π := by
  suffices H : ∀ a : PreTrace Loc Val A, Refines (Rg ∪ Rc) a π → IsTrace a →
      ∃ σ, Refines Rg a σ ∧ Refines Rc σ π from H τ h hτ
  intro a ha
  induction ha using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ ↦ ⟨_, Refines.refl _, Refines.refl _⟩
  | @head a b hab _ ih =>
      intro hta
      obtain ⟨σ, hg, hc⟩ := ih hab.2
      rcases hab.union_cases with hg' | hc'
      · exact ⟨σ, (Refines.single hg').trans hg, hc⟩
      · obtain ⟨σ', hgσ, hcσ⟩ := hcast.push hta hc' hg
        exact ⟨σ', hgσ, (Refines.single hcσ).trans hc⟩

/-- If `S` is already closed under the `Rg`-rewrites, closing it under
`Rg ∪ Rc` is the same as closing it under `Rc` alone.  This is what makes the
Concrete model's associativity reduce to the `𝔠`-model's. -/
theorem closure_eq_of_gClosed {Rc Rg : RuleSet} (hcast : Castles.{u} Rc Rg Loc Val)
    {S : Set (PreTrace Loc Val A)} (hS : IsTraceSet S) (hg : Closed Rg S) :
    closure (Rg ∪ Rc) S = closure Rc S := by
  refine Set.Subset.antisymm ?_ (closure_mono_rules Set.subset_union_right S)
  rintro π ⟨τ, hτ, hr⟩
  obtain ⟨σ, hgσ, hcσ⟩ := hr.sort hcast (hS τ hτ)
  exact ⟨σ, hg.mem_of_refines hτ hgσ, hcσ⟩

/-! ## The cases involving `Forward` and `Rewind`

Journal Appendix F, p.62: "The cases of `Fw ⇄ y` and `Rw ⇄ y` where `y ∈ 𝔤`
(13, 14, 15, 16, 17, 18) are trivial because the required condition remains the
same."  They are trivial for `Ls` and `Ex`, which do not touch the delimiting
views; for `Cn`, which pulls both of them, the reordered `Forward` (resp.
`Rewind`) needs Lemma 7.6 to know that pulling preserves `κ ⊑ ω`. -/

/-- Diagrams 13, 15, 17: `Fw ⇄ y` for `y ∈ 𝔤`. -/
theorem castle_forward {Rc Rg : RuleSet} (hg : Rg ⊆ gRules) (hFw : Rule.Fw ∈ Rc)
    {α κ ω : View Loc} {r : A} {c : Chro Loc Val} {τ₃ : PreTrace Loc Val A}
    (hκω : κ ≤ ω) (hτ₁ : IsTrace (⟨α, c, κ, r⟩ : PreTrace Loc Val A))
    (hτ₂ : IsTrace (⟨α, c, ω, r⟩ : PreTrace Loc Val A))
    (h₂ : Step Rg (⟨α, c, ω, r⟩ : PreTrace Loc Val A) τ₃) (hτ₃ : IsTrace τ₃) :
    ∃ τ₂', Step Rg (⟨α, c, κ, r⟩ : PreTrace Loc Val A) τ₂' ∧ IsTrace τ₂' ∧
      Step Rc τ₂' τ₃ := by
  cases h₂ with
  | chro hx hcs =>
      exact ⟨_, Step.chro hx hcs, isTrace_chroStep (hg hx) hcs hτ₁ hτ₃.wf,
        Step.forward hFw hκω⟩
  | forward hx _ => exact absurd (hg hx) (by simp)
  | rewind hx _ => exact absurd (hg hx) (by simp)
  | condense hx l m ν ε hde hfν hfε e₁ e₂ =>
      refine ⟨_, Step.condense hx l m ν ε hde hfν hfε e₁ e₂,
        isTrace_condense hde hfν hfε e₁ e₂ hτ₁ hτ₃.wf, Step.forward hFw ?_⟩
      exact condense_mono hde hfε e₁ e₂ hτ₃.wf hτ₁.closePts.toPointsInto
        hτ₂.closePts.toPointsInto hκω

/-- Diagrams 14, 16, 18: `Rw ⇄ y` for `y ∈ 𝔤`. -/
theorem castle_rewind {Rc Rg : RuleSet} (hg : Rg ⊆ gRules) (hRw : Rule.Rw ∈ Rc)
    {α κ ω : View Loc} {r : A} {c : Chro Loc Val} {τ₃ : PreTrace Loc Val A}
    (hακ : α ≤ κ) (hτ₁ : IsTrace (⟨κ, c, ω, r⟩ : PreTrace Loc Val A))
    (hτ₂ : IsTrace (⟨α, c, ω, r⟩ : PreTrace Loc Val A))
    (h₂ : Step Rg (⟨α, c, ω, r⟩ : PreTrace Loc Val A) τ₃) (hτ₃ : IsTrace τ₃) :
    ∃ τ₂', Step Rg (⟨κ, c, ω, r⟩ : PreTrace Loc Val A) τ₂' ∧ IsTrace τ₂' ∧
      Step Rc τ₂' τ₃ := by
  cases h₂ with
  | chro hx hcs =>
      exact ⟨_, Step.chro hx hcs, isTrace_chroStep (hg hx) hcs hτ₁ hτ₃.wf,
        Step.rewind hRw hακ⟩
  | forward hx _ => exact absurd (hg hx) (by simp)
  | rewind hx _ => exact absurd (hg hx) (by simp)
  | condense hx l m ν ε hde hfν hfε e₁ e₂ =>
      refine ⟨_, Step.condense hx l m ν ε hde hfν hfε e₁ e₂,
        isTrace_condense hde hfν hfε e₁ e₂ hτ₁ hτ₃.wf, Step.rewind hRw ?_⟩
      exact condense_mono hde hfε e₁ e₂ hτ₃.wf
        (hτ₂.openPts.toPointsInto.mono hτ₂.o_sub_c)
        (hτ₁.openPts.toPointsInto.mono hτ₁.o_sub_c) hακ

end Isotope.Elgot.RA
