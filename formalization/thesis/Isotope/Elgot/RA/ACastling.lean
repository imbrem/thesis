import Isotope.Elgot.RA.Mirror
import Isotope.Elgot.RA.Monad

/-!
# Rewrite Castling for the abstract rules

Dvir, Kammar and Lahav's **Lemma 8.3 (Rewrite Castling)** (journal §8.1, p.39)
covers a `9 × 9` grid of rule pairs, laid out in **Table 5** (journal p.62) as
66 numbered diagrams.  `Isotope/Elgot/RA/Castling.lean` proves diagrams 1–18,
the half with `x ∈ 𝔠` and `y ∈ 𝔤`.  This file starts on the other half, the one
with `x ∈ 𝔞`.

Table 5 is indexed with the *second* rule `y` down the side and the *first*
rule `x` across the top, so the `𝔞` columns are

| `y \ x` | `Ti` | `Ab` | `Di` |
|---|---|---|---|
| `Ls` | 19, 20 | 26, 27 | 33, 34, 35 |
| `Ex` | 21, 22 | 28, 29 | 36, 37, 38 |
| `Cn` | 23, 24, 25 | 30, 31, 32 | 39, 40, 41, 42 |
| `St` | 43, 44 | 45, 46 | 47, 48 |
| `Mu` | 49–52 | 53–56 | 57–60 |
| `Fw` | **61** | **63** | 65 |
| `Rw` | **62** | **64** | 66 |

**What is proved here: diagrams 61, 62, 63, 64** — `Ti ⇄ Fw`, `Ti ⇄ Rw`,
`Ab ⇄ Fw`, `Ab ⇄ Rw` — as the standalone lemmas `castle_tiAb_forward` and
`castle_tiAb_rewind`, and their packaging as
`castling_tiAb : Castles tiAbRules fwRwRules`.  The paper's own summary
(journal p.62) discusses diagrams 1–42 in prose and leaves 43–66 to the
attached figures; so, as elsewhere in this development, the proofs are ours.

The two facts that make these four cases work are isolated first, because they
are the `𝔞` analogues of what `Isotope/Elgot/RA/GTrace.lean` supplies for `𝔤`:

* `ChroStep.o_eq_tiAb` — `Ti` and `Ab` do not touch the chronicle's *opening*
  memory (they act at `⟨μ, ρ ⊎ {ν}⟩` and later, always on the closing side);
* `ChroStep.closePts_tiAb` — pointing downwards into the closing memory
  transfers *backwards* along `Ti` and `Ab`.  For `Ti` this is the paper's
  "pointing downwards into a memory is stable under 'loosening' a message
  within the memory" (journal p.62) read in the opposite direction, since `Ti`
  is `Ls` mirrored; for `Ab` it is stability "under changing a message's
  initial timestamp and adding a message within the memory" (ibid.).

**Not proved here**: diagrams 19–60 (`Ti`, `Ab`, `Di` against `Ls`, `Ex`, `Cn`,
`St`, `Mu`) and 65, 66 (`Di` against `Fw`, `Rw`).  See the honest boundary at
the foot of this file.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {A : Type u}

/-! ## An auxiliary rule set

(`tiAbRules` is defined in `Isotope/Elgot/RA/Mirror.lean`.) -/

/-- `{Fw, Rw}`: the two `𝔠` rules that act on the delimiting views alone.
Ours, not the paper's. -/
def fwRwRules : RuleSet := {Rule.Fw, Rule.Rw}

@[simp] theorem mem_fwRwRules {x : Rule} :
    x ∈ fwRwRules ↔ x = Rule.Fw ∨ x = Rule.Rw := by simp [fwRwRules]

theorem tiAbRules_subset_aRules : tiAbRules ⊆ aRules := by
  intro x hx
  simp only [mem_tiAbRules] at hx
  simp only [mem_aRules]
  tauto

theorem fwRwRules_subset_cRules : fwRwRules ⊆ cRules := by
  intro x hx
  simp only [mem_fwRwRules] at hx
  simp only [mem_cRules]
  tauto

/-! ## The two transfer facts for `Ti` and `Ab` -/

/-- `Ti` and `Ab` leave the chronicle's opening memory alone: they act at the
transition `⟨μ, ρ ⊎ {ν}⟩` and after it, always on the closing side. -/
theorem ChroStep.o_eq_tiAb {x : Rule} (hx : x ∈ tiAbRules) {c₁ c₂ : Chro Loc Val}
    (h : ChroStep x c₁ c₂) : c₁.o = c₂.o := by
  cases h with
  | stutter => simp at hx
  | mumble => simp at hx
  | loosen => simp at hx
  | expel => simp at hx
  | tighten _ _ l m μ ρ ν ε _ _ _ _ _ _ _ e₁ e₂ =>
      cases l with
      | nil => rw [Chro.o, Chro.o, e₁, e₂]; rfl
      | cons T l => rw [Chro.o, Chro.o, e₁, e₂]; rfl
  | absorb _ _ l m μ ρ ν ε _ _ _ _ _ _ _ _ _ _ e₁ e₂ =>
      cases l with
      | nil => rw [Chro.o, Chro.o, e₁, e₂]; rfl
      | cons T l => rw [Chro.o, Chro.o, e₁, e₂]; rfl

/-- Pointing downwards into the closing memory transfers *backwards* along `Ti`
and `Ab`: whatever points downwards into the target's closing memory points
downwards into the source's.

For `Ti` this is journal p.62's "pointing downwards into a memory is stable
under 'loosening' a message within the memory", read in the direction `Ti`
runs; for `Ab` it is "stable under changing a message's initial timestamp and
adding a message within the memory". -/
theorem ChroStep.closePts_tiAb {x : Rule} (hx : x ∈ tiAbRules) {c₁ c₂ : Chro Loc Val}
    (h : ChroStep x c₁ c₂) {κ : View Loc} (hκ : PointsDownInto κ c₂.c) :
    PointsDownInto κ c₁.c := by
  cases h with
  | stutter => simp at hx
  | mumble => simp at hx
  | loosen => simp at hx
  | expel => simp at hx
  | tighten _ _ l m μ ρ ν ε hle _ _ _ _ _ _ e₁ e₂ =>
      rcases exists_closing_of_aShape e₁ e₂ with ⟨-, f₁, f₂⟩ | ⟨U, _, f₁, f₂⟩
      · rw [f₂] at hκ
        rw [f₁]
        exact hκ.subst_insert hle.lc_eq hle.t_eq hle.vw_le
      · rw [f₂] at hκ
        rw [f₁]
        exact hκ.subst_insert hle.lc_eq hle.t_eq hle.vw_le
  | absorb _ _ l m μ ρ ν ε hdt _ _ _ _ _ _ _ _ _ e₁ e₂ =>
      rcases exists_closing_of_aShape e₁ e₂ with ⟨-, f₁, f₂⟩ | ⟨U, _, f₁, f₂⟩
      · rw [f₂] at hκ
        rw [f₁]
        exact (hκ.subst_insert (ν := ε) rfl rfl (le_refl _)).mono (Set.subset_insert _ _)
      · rw [f₂] at hκ
        rw [f₁]
        exact (hκ.subst_insert (ν := ε) rfl rfl (le_refl _)).mono (Set.subset_insert _ _)

/-! ## Diagrams 61–64 -/

/-- **Diagrams 61 and 63** (journal Table 5, p.62): `Ti ⇄ Fw` and `Ab ⇄ Fw`.
A `Ti`- or `Ab`-rewrite followed by a `Forward` is a `Forward` followed by the
same chronicle rewrite.  The intermediate pre-trace is a trace because `Ti` and
`Ab` do not touch the opening memory and pointing downwards into the closing
memory transfers backwards along them.

**Original work**: the paper leaves these diagrams to its figures. -/
theorem castle_tiAb_forward {Ra Rc : RuleSet} {x : Rule} (hx : x ∈ tiAbRules)
    (hxR : x ∈ Ra) (hFw : Rule.Fw ∈ Rc) {α κ ω : View Loc} {r : A}
    {c₁ c₂ : Chro Loc Val} (hcs : ChroStep x c₁ c₂) (hκω : κ ≤ ω)
    (hτ₁ : IsTrace (⟨α, c₁, κ, r⟩ : PreTrace Loc Val A))
    (hτ₃ : IsTrace (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A)) :
    ∃ τ₂' : PreTrace Loc Val A, Step Rc (⟨α, c₁, κ, r⟩ : PreTrace Loc Val A) τ₂' ∧
      IsTrace τ₂' ∧ Step Ra τ₂' (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A) := by
  refine ⟨⟨α, c₁, ω, r⟩, Step.forward hFw hκω, ⟨hτ₁.wf, hτ₁.openPts,
    le_trans hτ₁.mono hκω, hcs.closePts_tiAb hx hτ₃.closePts, ?_⟩, Step.chro hxR hcs⟩
  intro ν hν
  obtain ⟨h1, h2, h3⟩ := hτ₁.own ν hν
  exact ⟨h1, le_trans h2 hκω, h3⟩

/-- **Diagrams 62 and 64** (journal Table 5, p.62): `Ti ⇄ Rw` and `Ab ⇄ Rw`.

**Original work**: the paper leaves these diagrams to its figures. -/
theorem castle_tiAb_rewind {Ra Rc : RuleSet} {x : Rule} (hx : x ∈ tiAbRules)
    (hxR : x ∈ Ra) (hRw : Rule.Rw ∈ Rc) {α κ ω : View Loc} {r : A}
    {c₁ c₂ : Chro Loc Val} (hcs : ChroStep x c₁ c₂) (hακ : α ≤ κ)
    (hτ₁ : IsTrace (⟨κ, c₁, ω, r⟩ : PreTrace Loc Val A))
    (hτ₃ : IsTrace (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A)) :
    ∃ τ₂' : PreTrace Loc Val A, Step Rc (⟨κ, c₁, ω, r⟩ : PreTrace Loc Val A) τ₂' ∧
      IsTrace τ₂' ∧ Step Ra τ₂' (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A) := by
  refine ⟨⟨α, c₁, ω, r⟩, Step.rewind hRw hακ, ⟨hτ₁.wf, ?_, le_trans hακ hτ₁.mono,
    hτ₁.closePts, ?_⟩, Step.chro hxR hcs⟩
  · have := hτ₃.openPts
    change PointsDownInto α c₂.o at this
    change PointsDownInto α c₁.o
    rw [hcs.o_eq_tiAb hx]
    exact this
  · intro ν hν
    obtain ⟨h1, h2, h3⟩ := hτ₁.own ν hν
    exact ⟨le_trans hακ h1, h2, lt_of_le_of_lt (hακ ν.lc) h3⟩

/-! ## Packaging -/

/-- **Rewrite Castling for `{Ti, Ab}` past `{Fw, Rw}`** — diagrams 61–64 of
Table 5 (journal p.62).  A `Ti`- or `Ab`-rewrite followed by a `Forward` or
`Rewind`, both restricted to traces, is a `Forward` or `Rewind` followed by the
same chronicle rewrite. -/
theorem castling_tiAb : Castles.{u} tiAbRules fwRwRules Loc Val := by
  intro A τ₁ τ₂ τ₃ hτ₁ h₁ h₂
  obtain ⟨hstep₁, hτ₂⟩ := h₁
  obtain ⟨hstep₂, hτ₃⟩ := h₂
  cases hstep₁ with
  | chro hx hcs =>
      cases hstep₂ with
      | forward hy hκω =>
          obtain ⟨τ₂', hs, ht, hs'⟩ :=
            castle_tiAb_forward (by simpa using hx) hx (show Rule.Fw ∈ fwRwRules by simp)
              hcs hκω hτ₁ hτ₃
          exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
      | rewind hy hακ =>
          obtain ⟨τ₂', hs, ht, hs'⟩ :=
            castle_tiAb_rewind (by simpa using hx) hx (show Rule.Rw ∈ fwRwRules by simp)
              hcs hακ hτ₁ hτ₃
          exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
      | chro hy hcs₂ => cases hcs₂ <;> simp at hy
      | condense hy => exact absurd hy (by simp)
      | dilute hy => exact absurd hy (by simp)
  | forward hx _ => exact absurd hx (by simp)
  | rewind hx _ => exact absurd hx (by simp)
  | condense hx => exact absurd hx (by simp)
  | dilute hx => exact absurd hx (by simp)

/-! ## Diagrams 65 and 66: `Di` against `Fw` and `Rw`

`Dilute` pulls the delimiting views as well as the chronicle, so reordering it
past a `Forward` or a `Rewind` needs Lemma 7.6 — `View.pull_le_pull_of_scattered`
— to know that the pull of the weakened view is still above the pull of the
original.  The two memory identities the lemma's side conditions need are
isolated first. -/

theorem listO_aShape {f g : Transition Loc Val → Transition Loc Val}
    (l m : List (Transition Loc Val)) (T S : Transition Loc Val)
    (hTS : T.opening = S.opening) :
    listO (l ++ T :: m.map f) = listO (l ++ S :: m.map g) := by
  cases l with
  | nil => exact hTS
  | cons U l => rfl

/-- **The two memory identities of a `Dilute`.**  The source's opening memory is
the pull of the target's; its closing memory is the pull of the target's with
the diluted-in message `ε` removed; and `ν`, which dovetails into `ε`, is in the
target's closing memory.  These are exactly the side conditions of Lemma 7.6
(`View.pull_le_pull_of_scattered`) and of `PointsDownInto.pull`. -/
theorem dilute_memories {c₁ c₂ : Chro Loc Val} {l m : List (Transition Loc Val)}
    {μ ρ : Memory Loc Val} {ν ε : Msg Loc Val} (hde : Msg.DovetailEq ν ε)
    (hερ : ε ∉ ρ) (hνρ : ν ∉ ρ) (hfνm : listFree ν m) (hfεm : listFree ε m)
    (h₁ : c₁.toList =
      (l ++ ⟨μ, insert ν ρ⟩ :: m.map (Transition.insertMsg ν)).map (Transition.pull ε))
    (h₂ : c₂.toList =
      l ++ ⟨μ, insert ν (insert ε ρ)⟩ ::
        m.map (fun T ↦ (T.insertMsg ε).insertMsg ν)) :
    c₁.o = Memory.pull ε c₂.o ∧ c₁.c = Memory.pull ε (c₂.c \ {ε}) ∧ ν ∈ c₂.c := by
  have hne : ν ≠ ε := fun hc ↦ by
    rw [hc] at hde; exact absurd hde.1.2.1 (ne_of_gt ε.i_lt_t)
  obtain ⟨X, hX₁, hX₂, hXε⟩ :
      ∃ X : Memory Loc Val,
        listC (l ++ (⟨μ, insert ν ρ⟩ : Transition Loc Val) ::
            m.map (Transition.insertMsg ν)) = insert ν X ∧
          c₂.c = insert ν (insert ε X) ∧ ε ∉ X := by
    rcases listC_aShape (f := Transition.insertMsg ν)
        (g := fun T ↦ (T.insertMsg ε).insertMsg ν) l m ⟨μ, insert ν ρ⟩
        ⟨μ, insert ν (insert ε ρ)⟩ with ⟨-, e₁, e₂⟩ | ⟨U, hU, e₁, e₂⟩
    · exact ⟨ρ, e₁, by rw [Chro.c, h₂]; exact e₂, hερ⟩
    · exact ⟨U.closing, e₁, by rw [Chro.c, h₂]; exact e₂, (hfεm U hU).2⟩
  have hdiff : c₂.c \ {ε} = insert ν X := by
    rw [hX₂]
    ext x
    constructor
    · rintro ⟨hx, hxe⟩
      rcases hx with rfl | hx
      · exact Set.mem_insert _ _
      · rcases hx with rfl | hx
        · exact absurd rfl hxe
        · exact Set.mem_insert_of_mem _ hx
    · rintro (rfl | hx)
      · exact ⟨Set.mem_insert _ _, hne⟩
      · exact ⟨Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx),
          fun hc ↦ hXε (hc ▸ hx)⟩
  refine ⟨?_, ?_, hX₂ ▸ Set.mem_insert _ _⟩
  · rw [Chro.o, Chro.o, h₁, h₂, listO_map_pull ε (by simp)]
    exact congrArg (Memory.pull ε)
      (listO_aShape l m ⟨μ, insert ν ρ⟩ ⟨μ, insert ν (insert ε ρ)⟩ rfl)
  · rw [Chro.c, h₁, listC_map_pull ε (by simp), hX₁, hdiff]

/-- **Diagram 65** (journal Table 5, p.62): `Di ⇄ Fw`.

**Original work**: the paper leaves this diagram to its figures. -/
theorem castle_dilute_forward {Ra Rc : RuleSet} (hDi : Rule.Di ∈ Ra)
    (hFw : Rule.Fw ∈ Rc) {α ω ω₃ : View Loc} {r : A} {c₁ c₂ : Chro Loc Val}
    {l m : List (Transition Loc Val)} {μ ρ : Memory Loc Val} {ν ε : Msg Loc Val}
    (hde : Msg.DovetailEq ν ε) (hεμ : ε ∉ μ) (hερ : ε ∉ ρ) (hνρ : ν ∉ ρ)
    (hfνm : listFree ν m) (hfεm : listFree ε m)
    (h₁ : c₁.toList =
      (l ++ ⟨μ, insert ν ρ⟩ :: m.map (Transition.insertMsg ν)).map (Transition.pull ε))
    (h₂ : c₂.toList =
      l ++ ⟨μ, insert ν (insert ε ρ)⟩ ::
        m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (hωω : ω ≤ ω₃)
    (hτ₁ : IsTrace (⟨View.pull ε α, c₁, View.pull ε ω, r⟩ : PreTrace Loc Val A))
    (hτ₂ : IsTrace (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A))
    (hτ₃ : IsTrace (⟨α, c₂, ω₃, r⟩ : PreTrace Loc Val A)) :
    ∃ τ₂' : PreTrace Loc Val A,
      Step Rc (⟨View.pull ε α, c₁, View.pull ε ω, r⟩ : PreTrace Loc Val A) τ₂' ∧
        IsTrace τ₂' ∧ Step Ra τ₂' (⟨α, c₂, ω₃, r⟩ : PreTrace Loc Val A) := by
  obtain ⟨hoe, hce, hνc⟩ := dilute_memories hde hερ hνρ hfνm hfεm h₁ h₂
  have hsc : Scattered c₁.c := hτ₁.scattered_c
  have hsub : Memory.pull ε (c₂.c \ {ε}) ⊆ c₁.c := by rw [hce]
  have hle : View.pull ε ω ≤ View.pull ε ω₃ :=
    View.pull_le_pull_of_scattered hsc hsub hτ₂.closePts.toPointsInto
      hτ₃.closePts.toPointsInto hωω
  refine ⟨⟨View.pull ε α, c₁, View.pull ε ω₃, r⟩, Step.forward hFw hle,
    ⟨hτ₁.wf, hτ₁.openPts, le_trans hτ₁.mono hle, ?_, ?_⟩,
    Step.dilute hDi l m μ ρ ν ε hde hεμ hερ hνρ hfνm hfεm h₁ h₂⟩
  · have := PointsDownInto.pull (ε := ε) hτ₃.wf_c hsc hsub
      (fun _ ↦ ⟨ν, hνc, hde.1⟩) hτ₃.closePts
    rw [← hce] at this
    exact this
  · intro ϑ hϑ
    obtain ⟨g1, g2, g3⟩ := hτ₁.own ϑ hϑ
    exact ⟨g1, le_trans g2 hle, g3⟩

/-- **Diagram 66** (journal Table 5, p.62): `Di ⇄ Rw`.

**Original work**: the paper leaves this diagram to its figures. -/
theorem castle_dilute_rewind {Ra Rc : RuleSet} (hDi : Rule.Di ∈ Ra)
    (hRw : Rule.Rw ∈ Rc) {α α₃ ω : View Loc} {r : A} {c₁ c₂ : Chro Loc Val}
    {l m : List (Transition Loc Val)} {μ ρ : Memory Loc Val} {ν ε : Msg Loc Val}
    (hde : Msg.DovetailEq ν ε) (hεμ : ε ∉ μ) (hερ : ε ∉ ρ) (hνρ : ν ∉ ρ)
    (hfνm : listFree ν m) (hfεm : listFree ε m)
    (h₁ : c₁.toList =
      (l ++ ⟨μ, insert ν ρ⟩ :: m.map (Transition.insertMsg ν)).map (Transition.pull ε))
    (h₂ : c₂.toList =
      l ++ ⟨μ, insert ν (insert ε ρ)⟩ ::
        m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (hαα : α₃ ≤ α)
    (hτ₁ : IsTrace (⟨View.pull ε α, c₁, View.pull ε ω, r⟩ : PreTrace Loc Val A))
    (hτ₂ : IsTrace (⟨α, c₂, ω, r⟩ : PreTrace Loc Val A))
    (hτ₃ : IsTrace (⟨α₃, c₂, ω, r⟩ : PreTrace Loc Val A)) :
    ∃ τ₂' : PreTrace Loc Val A,
      Step Rc (⟨View.pull ε α, c₁, View.pull ε ω, r⟩ : PreTrace Loc Val A) τ₂' ∧
        IsTrace τ₂' ∧ Step Ra τ₂' (⟨α₃, c₂, ω, r⟩ : PreTrace Loc Val A) := by
  obtain ⟨hoe, hce, hνc⟩ := dilute_memories hde hερ hνρ hfνm hfεm h₁ h₂
  have hsco : Scattered c₁.o := hτ₁.wf_o.scattered
  have hsubo : Memory.pull ε (c₂.o \ {ε}) ⊆ c₁.o := by
    rw [hoe]; exact Memory.pull_mono (fun _ hx ↦ hx.1)
  have hle : View.pull ε α₃ ≤ View.pull ε α :=
    View.pull_le_pull_of_scattered hsco hsubo
      hτ₃.openPts.toPointsInto hτ₂.openPts.toPointsInto hαα
  refine ⟨⟨View.pull ε α₃, c₁, View.pull ε ω, r⟩, Step.rewind hRw hle,
    ⟨hτ₁.wf, ?_, le_trans hle hτ₁.mono, hτ₁.closePts, ?_⟩,
    Step.dilute hDi l m μ ρ ν ε hde hεμ hερ hνρ hfνm hfεm h₁ h₂⟩
  · have := PointsDownInto.pull_all (ε := ε) hτ₃.wf_o (by rw [← hoe]; exact hsco)
      hτ₃.openPts
    rw [← hoe] at this
    exact this
  · intro ϑ hϑ
    obtain ⟨g1, g2, g3⟩ := hτ₁.own ϑ hϑ
    exact ⟨le_trans hle g1, g2, lt_of_le_of_lt (hle ϑ.lc) g3⟩

/-! ## Packaging the `𝔞`-past-`{Fw, Rw}` column -/

/-- A chronicle rewrite by a rule of `𝔞` is a `Ti` or an `Ab`: `Di` is not a
chronicle rewrite, since it pulls the delimiting views too. -/
theorem ChroStep.tiAb_of_a {x : Rule} {c₁ c₂ : Chro Loc Val} (hx : x ∈ aRules)
    (h : ChroStep x c₁ c₂) : x ∈ tiAbRules := by
  cases h <;> simp_all

/-- **Rewrite Castling for `𝔞` past `{Fw, Rw}`** — the whole bottom-right block
of Table 5 (journal p.62), diagrams 61–66.  Any `𝔞`-rewrite followed by a
`Forward` or a `Rewind`, both restricted to traces, is a `Forward` or `Rewind`
followed by the same `𝔞`-rewrite.

This is a proper part of the paper's Lemma 8.3 (`x ∈ 𝔞`, `y ∈ 𝔤𝔠`); the columns
of Table 5 for `y ∈ {Ls, Ex, Cn, St, Mu}` — diagrams 19–60 — are not proved
here. -/
theorem castling_a_fwRw : Castles.{u} aRules fwRwRules Loc Val := by
  intro A τ₁ τ₂ τ₃ hτ₁ h₁ h₂
  obtain ⟨hstep₁, hτ₂⟩ := h₁
  obtain ⟨hstep₂, hτ₃⟩ := h₂
  cases hstep₁ with
  | chro hx hcs =>
      cases hstep₂ with
      | forward hy hκω =>
          obtain ⟨τ₂', hs, ht, hs'⟩ :=
            castle_tiAb_forward (hcs.tiAb_of_a hx) hx (show Rule.Fw ∈ fwRwRules by simp)
              hcs hκω hτ₁ hτ₃
          exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
      | rewind hy hακ =>
          obtain ⟨τ₂', hs, ht, hs'⟩ :=
            castle_tiAb_rewind (hcs.tiAb_of_a hx) hx (show Rule.Rw ∈ fwRwRules by simp)
              hcs hακ hτ₁ hτ₃
          exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
      | chro hy hcs₂ => cases hcs₂ <;> simp at hy
      | condense hy => exact absurd hy (by simp)
      | dilute hy => exact absurd hy (by simp)
  | forward hx _ => exact absurd hx (by simp)
  | rewind hx _ => exact absurd hx (by simp)
  | condense hx => exact absurd hx (by simp)
  | dilute hx l m μ ρ ν ε hde hεμ hερ hνρ hfν hfε e₁ e₂ =>
      cases hstep₂ with
      | forward hy hκω =>
          obtain ⟨τ₂', hs, ht, hs'⟩ :=
            castle_dilute_forward hx (show Rule.Fw ∈ fwRwRules by simp) hde hεμ hερ hνρ
              hfν hfε e₁ e₂ hκω hτ₁ hτ₂ hτ₃
          exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
      | rewind hy hακ =>
          obtain ⟨τ₂', hs, ht, hs'⟩ :=
            castle_dilute_rewind hx (show Rule.Rw ∈ fwRwRules by simp) hde hεμ hερ hνρ
              hfν hfε e₁ e₂ hακ hτ₁ hτ₂ hτ₃
          exact ⟨τ₂', Refines.single ⟨hs, ht⟩, hs', hτ₃⟩
      | chro hy hcs₂ => cases hcs₂ <;> simp at hy
      | condense hy => exact absurd hy (by simp)
      | dilute hy => exact absurd hy (by simp)

/-- The rearrangement Rewrite Castling is introduced for (journal p.39), in the
range this file reaches: every `{Fw, Rw} ∪ 𝔞`-rewrite sequence factors as
`Forward`/`Rewind` rewrites followed by `𝔞`-rewrites. -/
theorem Refines.sort_a_fwRw {τ π : PreTrace Loc Val A} (hτ : IsTrace τ)
    (h : Refines (fwRwRules ∪ aRules) τ π) :
    ∃ σ, Refines fwRwRules τ σ ∧ Refines aRules σ π :=
  h.sort castling_a_fwRw hτ

end Isotope.Elgot.RA
