import Isotope.Elgot.RA.GData
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

⚠ One point of the reading of `Condense` is load-bearing here: its rewritten
suffix may be empty, so that the rule may pull a whole pre-trace along a
message occurring nowhere in it (see item 10 of the honest boundary in
`Isotope/Elgot/RA.lean`).  In `castle_stutter` the inserted stutter transition
can be the only one carrying `ε`, and then the castled `Cn`-rewrite is exactly
such a pure pull; with the stricter reading this case would be false.

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

/-! ## The cases involving `Stutter`

Journal Appendix F, p.62, diagrams 1–6: "For cases of `St ⇄ y` where `y ∈ 𝔤`
the required condition is about the same chronicle as the assumed condition,
except for possibly a removed transition."  Diagrams 1 and 2 (p.63) split the
`Ls` case according to whether the loosen'ee appears across the stutter'ee;
that is the case split below on where the inserted transition falls relative to
the rewritten suffix. -/

/-- Diagrams 1–6: `St ⇄ y` for `y ∈ 𝔤`, uniformly in the rule via `GData`. -/
theorem castle_stutter {Rc Rg : RuleSet} (hSt : Rule.St ∈ Rc)
    {α ω : View Loc} {r : A} {c₁ c₂ c₃ : Chro Loc Val}
    (D : GData Rg (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A) c₃)
    {X Y : List (Transition Loc Val)} {μ : Memory Loc Val}
    (e₁ : c₁.toList = X ++ Y) (e₂ : c₂.toList = X ++ (⟨μ, μ⟩ : Transition Loc Val) :: Y)
    (hτ₁ : IsTrace (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A))
    (hτ₃ : IsTrace (⟨D.hv α, c₃, D.hv ω, r⟩ : PreTrace Loc Val A)) :
    ∃ τ₂', Step Rg (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A) τ₂' ∧ IsTrace τ₂' ∧
      Step Rc τ₂' (⟨D.hv α, c₃, D.hv ω, r⟩ : PreTrace Loc Val A) := by
  have hsrc : X ++ (⟨μ, μ⟩ : Transition Loc Val) :: Y = D.l ++ D.m.map D.f := by
    rw [← e₂]; exact D.src
  have htgt : c₃.toList = D.l.map D.h ++ D.m.map D.g := D.tgt
  suffices H : ∃ (l' m' P Q : List (Transition Loc Val)) (μ' : Memory Loc Val),
      (∀ T ∈ m', D.free T) ∧ c₁.toList = l' ++ m'.map D.f ∧
      l'.map D.h ++ m'.map D.g = P ++ Q ∧
      c₃.toList = P ++ (⟨μ', μ'⟩ : Transition Loc Val) :: Q by
    obtain ⟨l', m', P, Q, μ', hm', he₁, hPQ, hc₃⟩ := H
    have hchain : List.IsChain Adj (P ++ Q) := by
      refine isChain_remove_mid (T := ⟨μ', μ'⟩) ?_ (subset_refl _)
      rw [← hc₃]; exact c₃.chain_toList
    have hne : P ++ Q ≠ [] := by
      intro hc
      refine c₁.toList_ne_nil ?_
      have hlen : (l'.map D.h ++ m'.map D.g).length = 0 := by rw [hPQ, hc]; rfl
      simp only [List.length_append, List.length_map] at hlen
      have h1 : l' = [] := List.eq_nil_of_length_eq_zero (by omega)
      have h2 : m' = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [he₁, h1, h2]; rfl
    have hofl : (Chro.ofList (P ++ Q) hne hchain).toList = P ++ Q :=
      Chro.ofList_toList _ _ _
    have he₂ : (Chro.ofList (P ++ Q) hne hchain).toList = l'.map D.h ++ m'.map D.g := by
      rw [hofl]; exact hPQ.symm
    refine ⟨⟨D.hv α, Chro.ofList (P ++ Q) hne hchain, D.hv ω, r⟩,
      D.mk_step α ω r c₁ _ l' m' hm' he₁ he₂, ?_, ?_⟩
    · refine D.mk_trace α ω r c₁ _ l' m' hm' he₁ he₂ hτ₁ ?_
      intro T hT
      refine hτ₃.wf T ?_
      change T ∈ c₃.toList
      rw [hc₃, hofl] at *
      rcases List.mem_append.mp hT with h | h
      · exact List.mem_append.mpr (Or.inl h)
      · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ h))
    · exact Step.chro hSt (ChroStep.stutter _ c₃ P Q μ' hofl hc₃)
  rcases List.append_eq_append_iff.mp hsrc with ⟨as, hl, hxy⟩ | ⟨bs, hX, hm⟩
  · cases as with
    | nil =>
        rw [List.nil_append] at hxy
        obtain ⟨S, m₁, hmeq, hfS, hm₁⟩ := List.map_eq_cons_iff.mp hxy.symm
        obtain ⟨μ', hgS⟩ := D.fg_stutter S (D.hfree S (by rw [hmeq]; simp)) μ hfS
        refine ⟨D.l, m₁, D.l.map D.h, m₁.map D.g, μ',
          fun T hT ↦ D.hfree T (by rw [hmeq]; simp [hT]), ?_, rfl, ?_⟩
        · rw [e₁, hl, List.append_nil, hm₁]
        · rw [htgt, hmeq, List.map_cons, hgS]
    | cons T as' =>
        rw [List.cons_append, List.cons.injEq] at hxy
        obtain ⟨hT, hY⟩ := hxy
        obtain ⟨μ', hhT⟩ := D.h_stutter μ
        refine ⟨X ++ as', D.m, X.map D.h, as'.map D.h ++ D.m.map D.g, μ',
          fun T' hT' ↦ D.hfree T' hT', ?_, ?_, ?_⟩
        · rw [e₁, hY, List.append_assoc]
        · rw [List.map_append, List.append_assoc]
        · rw [htgt, hl, List.map_append, List.map_cons, ← hT, hhT]
          simp [List.append_assoc]
  · obtain ⟨m₁, m₂, hmeq, hm₁, hm₂⟩ := List.map_eq_append_iff.mp hm
    obtain ⟨S, m₃, hm₂eq, hfS, hm₃⟩ := List.map_eq_cons_iff.mp hm₂
    obtain ⟨μ', hgS⟩ := D.fg_stutter S
      (D.hfree S (by rw [hmeq, hm₂eq]; simp)) μ hfS
    refine ⟨D.l, m₁ ++ m₃, D.l.map D.h ++ m₁.map D.g, m₃.map D.g, μ',
      fun T hT ↦ D.hfree T (by
        rw [hmeq, hm₂eq]
        rcases List.mem_append.mp hT with h | h
        · simp [h]
        · simp [h]), ?_, ?_, ?_⟩
    · rw [e₁, hX, ← hm₁, ← hm₃]
      simp [List.map_append, List.append_assoc]
    · simp [List.map_append, List.append_assoc]
    · rw [htgt, hmeq, hm₂eq]
      simp [List.map_append, List.map_cons, hgS, List.append_assoc]

/-! ## The cases involving `Mumble`

Journal Appendix F, p.62, diagrams 7–12: "Cases of `Mu ⇄ y` where `y ∈ 𝔤` are
simpler because the opening and closing memory remain the same."  What they do
require, and what the paper does not comment on, is that the *intermediate*
memory of the un-mumbled pair is well-formed after the `𝔤`-rewrite; that is the
`WellFormed` clause of `GData.h_mumble` and `GData.fg_mumble`, proved there by
sandwiching it between the two memories of the mumbled transition. -/

/-- Diagrams 7–12: `Mu ⇄ y` for `y ∈ 𝔤`, uniformly in the rule via `GData`. -/
theorem castle_mumble {Rc Rg : RuleSet} (hMu : Rule.Mu ∈ Rc)
    {α ω : View Loc} {r : A} {c₁ c₂ c₃ : Chro Loc Val}
    (D : GData Rg (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A) c₃)
    {X Y : List (Transition Loc Val)} {a b c : Memory Loc Val}
    (e₁ : c₁.toList = X ++ (⟨a, b⟩ : Transition Loc Val) :: ⟨b, c⟩ :: Y)
    (e₂ : c₂.toList = X ++ (⟨a, c⟩ : Transition Loc Val) :: Y)
    (hτ₁ : IsTrace (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A))
    (hτ₃ : IsTrace (⟨D.hv α, c₃, D.hv ω, r⟩ : PreTrace Loc Val A)) :
    ∃ τ₂', Step Rg (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A) τ₂' ∧ IsTrace τ₂' ∧
      Step Rc τ₂' (⟨D.hv α, c₃, D.hv ω, r⟩ : PreTrace Loc Val A) := by
  have hmem₁ : (⟨a, b⟩ : Transition Loc Val) ∈ c₁.toList := by rw [e₁]; simp
  have hmem₂ : (⟨b, c⟩ : Transition Loc Val) ∈ c₁.toList := by rw [e₁]; simp
  have hab : a ⊆ b := (hτ₁.wf _ hmem₁).sub
  have hbc : b ⊆ c := (hτ₁.wf _ hmem₂).sub
  have hwfb : WellFormed b := (hτ₁.wf _ hmem₁).closing
  have hsrc : X ++ (⟨a, c⟩ : Transition Loc Val) :: Y = D.l ++ D.m.map D.f := by
    rw [← e₂]; exact D.src
  have htgt : c₃.toList = D.l.map D.h ++ D.m.map D.g := D.tgt
  suffices H : ∃ (l' m' P Q : List (Transition Loc Val)) (u v w : Memory Loc Val),
      (∀ T ∈ m', D.free T) ∧ c₁.toList = l' ++ m'.map D.f ∧
      l'.map D.h ++ m'.map D.g = P ++ (⟨u, v⟩ : Transition Loc Val) :: ⟨v, w⟩ :: Q ∧
      c₃.toList = P ++ (⟨u, w⟩ : Transition Loc Val) :: Q ∧
      WellFormed v ∧ u ⊆ v ∧ v ⊆ w by
    obtain ⟨l', m', P, Q, u, v, w, hm', he₁, hL, hc₃, hwfv, huv, hvw⟩ := H
    have hwfuw : Transition.WF (⟨u, w⟩ : Transition Loc Val) :=
      hτ₃.wf _ (by change (⟨u, w⟩ : Transition Loc Val) ∈ c₃.toList; rw [hc₃]; simp)
    have hchain : List.IsChain Adj
        (P ++ (⟨u, v⟩ : Transition Loc Val) :: ⟨v, w⟩ :: Q) := by
      refine isChain_split_mid (a := u) (c := w) ?_
      rw [← hc₃]; exact c₃.chain_toList
    have hne : P ++ (⟨u, v⟩ : Transition Loc Val) :: ⟨v, w⟩ :: Q ≠ [] := by simp
    have hofl : (Chro.ofList _ hne hchain).toList =
        P ++ (⟨u, v⟩ : Transition Loc Val) :: ⟨v, w⟩ :: Q := Chro.ofList_toList _ _ _
    have he₂ : (Chro.ofList _ hne hchain).toList = l'.map D.h ++ m'.map D.g := by
      rw [hofl]; exact hL.symm
    refine ⟨⟨D.hv α, Chro.ofList _ hne hchain, D.hv ω, r⟩,
      D.mk_step α ω r c₁ _ l' m' hm' he₁ he₂, ?_, ?_⟩
    · refine D.mk_trace α ω r c₁ _ l' m' hm' he₁ he₂ hτ₁ ?_
      intro T hT
      rw [hofl] at hT
      rcases List.mem_append.mp hT with h | h
      · exact hτ₃.wf T (by change T ∈ c₃.toList; rw [hc₃]; simp [h])
      · rcases List.mem_cons.mp h with rfl | h
        · exact ⟨hwfuw.opening, hwfv, huv⟩
        · rcases List.mem_cons.mp h with rfl | h
          · exact ⟨hwfv, hwfuw.closing, hvw⟩
          · exact hτ₃.wf T (by change T ∈ c₃.toList; rw [hc₃]; simp [h])
    · exact Step.chro hMu (ChroStep.mumble _ c₃ P Q u v w hofl hc₃)
  rcases List.append_eq_append_iff.mp hsrc with ⟨as, hl, hxy⟩ | ⟨bs, hX, hm⟩
  · cases as with
    | nil =>
        rw [List.nil_append] at hxy
        obtain ⟨S, m₁, hmeq, hfS, hm₁⟩ := List.map_eq_cons_iff.mp hxy.symm
        have hgSmem : D.g S ∈ c₃.toList := by rw [htgt, hmeq]; simp
        obtain ⟨S₁, S₂, hfr₁, hfr₂, hfS₁, hfS₂, ho1, hc2, hv12, hwfv, hsub1, hsub2⟩ :=
          D.fg_mumble S (D.hfree S (by rw [hmeq]; simp)) a b c hfS hab hbc hwfb
            (hτ₃.wf _ hgSmem).opening (hτ₃.wf _ hgSmem).closing
        have hgS₁ : D.g S₁ = ⟨(D.g S).opening, (D.g S₁).closing⟩ := by rw [← ho1]
        have hgS₂ : D.g S₂ = ⟨(D.g S₁).closing, (D.g S).closing⟩ := by rw [hv12, ← hc2]
        have hgS : D.g S = ⟨(D.g S).opening, (D.g S).closing⟩ := rfl
        refine ⟨D.l, S₁ :: S₂ :: m₁, D.l.map D.h, m₁.map D.g,
          (D.g S).opening, (D.g S₁).closing, (D.g S).closing, ?_, ?_, ?_, ?_,
          hwfv, hsub1, hsub2⟩
        · intro T hT
          rcases List.mem_cons.mp hT with rfl | hT
          · exact hfr₁
          · rcases List.mem_cons.mp hT with rfl | hT
            · exact hfr₂
            · exact D.hfree T (by rw [hmeq]; simp [hT])
        · rw [e₁, hl, List.append_nil, List.map_cons, List.map_cons, hfS₁, hfS₂, hm₁]
        · rw [List.map_cons, List.map_cons, ← hgS₁, ← hgS₂]
        · rw [htgt, hmeq, List.map_cons, ← hgS]
    | cons T as' =>
        rw [List.cons_append, List.cons.injEq] at hxy
        obtain ⟨hT, hY⟩ := hxy
        obtain ⟨ho1, hc2, hv12, hwfv, hsub1, hsub2⟩ := D.h_mumble a b c hab hbc hwfb
          (by
            refine (hτ₃.wf _ ?_).opening
            rw [htgt, hl, List.map_append, List.map_cons, ← hT]; simp)
          (by
            refine (hτ₃.wf _ ?_).closing
            rw [htgt, hl, List.map_append, List.map_cons, ← hT]; simp)
        have hh₁ : D.h ⟨a, b⟩ = ⟨(D.h ⟨a, c⟩).opening, (D.h ⟨a, b⟩).closing⟩ := by rw [← ho1]
        have hh₂ : D.h ⟨b, c⟩ = ⟨(D.h ⟨a, b⟩).closing, (D.h ⟨a, c⟩).closing⟩ := by
          rw [hv12, ← hc2]
        have hh : D.h ⟨a, c⟩ = ⟨(D.h ⟨a, c⟩).opening, (D.h ⟨a, c⟩).closing⟩ := rfl
        refine ⟨X ++ ⟨a, b⟩ :: ⟨b, c⟩ :: as', D.m, X.map D.h,
          as'.map D.h ++ D.m.map D.g, (D.h ⟨a, c⟩).opening, (D.h ⟨a, b⟩).closing,
          (D.h ⟨a, c⟩).closing, fun T' hT' ↦ D.hfree T' hT', ?_, ?_, ?_,
          hwfv, hsub1, hsub2⟩
        · rw [e₁, hY]
          simp [List.append_assoc]
        · rw [List.map_append, List.map_cons, List.map_cons, ← hh₁, ← hh₂]
          simp [List.append_assoc]
        · rw [htgt, hl, List.map_append, List.map_cons, ← hT, ← hh]
          simp [List.append_assoc]
  · obtain ⟨m₁, m₂, hmeq, hm₁, hm₂⟩ := List.map_eq_append_iff.mp hm
    obtain ⟨S, m₃, hm₂eq, hfS, hm₃⟩ := List.map_eq_cons_iff.mp hm₂
    have hSmem : S ∈ D.m := by rw [hmeq, hm₂eq]; simp
    have hgSmem : D.g S ∈ c₃.toList := by rw [htgt, hmeq, hm₂eq]; simp
    obtain ⟨S₁, S₂, hfr₁, hfr₂, hfS₁, hfS₂, ho1, hc2, hv12, hwfv, hsub1, hsub2⟩ :=
      D.fg_mumble S (D.hfree S hSmem) a b c hfS hab hbc hwfb
        (hτ₃.wf _ hgSmem).opening (hτ₃.wf _ hgSmem).closing
    have hgS₁ : D.g S₁ = ⟨(D.g S).opening, (D.g S₁).closing⟩ := by rw [← ho1]
    have hgS₂ : D.g S₂ = ⟨(D.g S₁).closing, (D.g S).closing⟩ := by rw [hv12, ← hc2]
    have hgS : D.g S = ⟨(D.g S).opening, (D.g S).closing⟩ := rfl
    refine ⟨D.l, m₁ ++ S₁ :: S₂ :: m₃, D.l.map D.h ++ m₁.map D.g, m₃.map D.g,
      (D.g S).opening, (D.g S₁).closing, (D.g S).closing, ?_, ?_, ?_, ?_,
      hwfv, hsub1, hsub2⟩
    · intro T hT
      rcases List.mem_append.mp hT with h | h
      · exact D.hfree T (by rw [hmeq]; simp [h])
      · rcases List.mem_cons.mp h with rfl | h
        · exact hfr₁
        · rcases List.mem_cons.mp h with rfl | h
          · exact hfr₂
          · exact D.hfree T (by rw [hmeq, hm₂eq]; simp [h])
    · rw [e₁, hX, ← hm₁, ← hm₃]
      simp [List.map_append, List.map_cons, hfS₁, hfS₂, List.append_assoc]
    · rw [← hgS₁, ← hgS₂]
      simp [List.map_append, List.map_cons, List.append_assoc]
    · rw [htgt, hmeq, hm₂eq, ← hgS]
      simp [List.map_append, List.map_cons, List.append_assoc]

/-! ## Rewrite Castling for `𝔠` past `𝔤` -/

/-- **Rewrite Castling** (journal Lemma 8.3, p.39), for `x ∈ 𝔠` and `y ∈ 𝔤`:
the twelve cases of Table 5 numbered 1–18.  A `𝔠`-rewrite followed by a
`𝔤`-rewrite, both restricted to traces, is a `𝔤`-rewrite followed by a
`𝔠`-rewrite.

The `𝔞` half of Lemma 8.3 (`x ∈ 𝔞`, diagrams 19–66) is out of scope: the group
`𝔞` is not formalized. -/
theorem castling : Castles.{u} cRules gRules Loc Val := by
  intro A τ₁ τ₂ τ₃ hτ₁ h₁ h₂
  obtain ⟨hstep₁, hτ₂⟩ := h₁
  obtain ⟨hstep₂, hτ₃⟩ := h₂
  cases hstep₁ with
  | chro hx hcs =>
      obtain ⟨c₃, D, rfl⟩ := exists_gData (subset_refl gRules) hstep₂ hτ₃
      cases hcs with
      | stutter _ _ P Q μ e₁ e₂ =>
          obtain ⟨τ₂', hs, ht, hs'⟩ :=
            castle_stutter (show Rule.St ∈ cRules by simp) D e₁ e₂ hτ₁ hτ₃
          exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
      | mumble _ _ P Q a b c e₁ e₂ =>
          obtain ⟨τ₂', hs, ht, hs'⟩ :=
            castle_mumble (show Rule.Mu ∈ cRules by simp) D e₁ e₂ hτ₁ hτ₃
          exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
      | loosen => exact absurd hx (by simp)
      | expel => exact absurd hx (by simp)
  | forward hx hκω =>
      obtain ⟨τ₂', hs, ht, hs'⟩ :=
        castle_forward (subset_refl gRules) hx hκω hτ₁ hτ₂ hstep₂ hτ₃
      exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
  | rewind hx hακ =>
      obtain ⟨τ₂', hs, ht, hs'⟩ :=
        castle_rewind (subset_refl gRules) hx hακ hτ₁ hτ₂ hstep₂ hτ₃
      exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
  | condense hx => exact absurd hx (by simp)

/-- The paper's rearrangement (journal p.39) at `𝔤𝔠`: every `𝔤𝔠`-rewrite
sequence factors as `𝔤`-rewrites followed by `𝔠`-rewrites. -/
theorem Refines.sort_gc {τ π : PreTrace Loc Val A} (hτ : IsTrace τ)
    (h : Refines gcRules τ π) : ∃ σ, Refines gRules τ σ ∧ Refines cRules σ π :=
  h.sort castling hτ

/-- **For a `𝔤`-closed set of traces, closing under `𝔤𝔠` is closing under
`𝔠`.**  This is the form in which Rewrite Castling is used: together with
Proposition 7.5 it reduces the Concrete model to the `𝔠`-model. -/
theorem closure_gcRules_eq {S : Set (PreTrace Loc Val A)} (hS : IsTraceSet S)
    (hg : Closed gRules S) : closure gcRules S = closure cRules S :=
  closure_eq_of_gClosed castling hS hg

end Isotope.Elgot.RA
