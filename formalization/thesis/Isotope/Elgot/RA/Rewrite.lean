import Isotope.Elgot.RA.Trace

/-!
# The rewrite rules, indexed by rule sets

Dvir, Kammar and Lahav (`release-acquire`) parameterize their whole development
by a set `★` of closure rules (Table 2 of the TOPLAS journal version, Table 1 of
the ESOP version) and obtain a tower of models by varying it (journal Table 1,
p.29):

| model | `★` | monad? |
|---|---|---|
| Null `N` | `∅` | no |
| Generating `G` | `𝔤 = {Ls, Ex, Cn}` | no |
| Concrete `C` (ESOP's `M`) | `𝔤𝔠 = 𝔤 ∪ 𝔠` | Prop. 7.7 |
| Abstract `A` | `𝔤𝔠𝔞` | Prop. 7.8 |

This file transcribes all nine rules of Table 2: the *generating* group `𝔤`,
the *concrete* group `𝔠 = {St, Mu, Fw, Rw}` and the *abstract* group
`𝔞 = {Ti, Ab, Di}`, and indexes the one-step rewrite relation by an arbitrary
`RuleSet`, so that everything downstream is proved once for all models.

## The rules, verbatim (journal Table 2, p.30, read from the typeset table)

```
Stutter  (St)   α ξη ω               →  α ξ ⟨μ,μ⟩ η ω
Mumble   (Mu)   α ξ ⟨μ,ρ⟩⟨ρ,θ⟩ η ω   →  α ξ ⟨μ,θ⟩ η ω
Forward  (Fw)   α ξ κ ◁ r            →  α ξ ω ◁ r                if κ ⊑ ω
Rewind   (Rw)   κ ξ ω ◁ r            →  α ξ ω ◁ r                if α ⊑ κ
Loosen   (Ls)   α ξ (η ⊎ {ε}) ω      →  α ξ (η ⊎ {ν}) ω          if ν ≤vw ε
Expel    (Ex)   α ξ (η ⊎ {ε[i↦ν.i]}) ω → α ξ (η ⊎ {ν, ε}) ω      if ν ⤙ ε
Condense (Cn)   α ξ (η ⊎ {ν, ε}) ω   →  (α ξ (η ⊎ {ν}) ω)[↑ε]    if ν ⤙= ε
Tighten  (Ti)   α ξ⟨μ, ρ⊎{ν}⟩ η⊎{ν} ω         →  α ξ⟨μ, ρ⊎{ε}⟩ η⊎{ε} ω              if ν ≤vw ε
Absorb   (Ab)   α ξ⟨μ, ρ⊎{ν,ε}⟩ η⊎{ν,ε} ω     →  α ξ⟨μ, ρ⊎{ε[i↦ν.i]}⟩ η⊎{ε[i↦ν.i]} ω  if ν ⤙ ε
Dilute   (Di)  (α ξ⟨μ, ρ⊎{ν}⟩ η⊎{ν} ω)[↑ε]   →  α ξ⟨μ, ρ⊎{ν,ε}⟩ η⊎{ν,ε} ω          if ν ⤙= ε
```

The three `𝔞` rows were read off the typeset Table 2 (journal p.30) and the
displays `(Tighten)`, `(Absorb)` (journal p.36) and `(Dilute)` (journal p.37)
directly, by rendering those pages; the `pdftotext` extractions garble them.
Note that the paper distinguishes the memory-level `⊎` from a *barred* `⊎` at
the chronicle level, which is the `η ⊎ {ν}` of the table above.

## The `𝔞`-shape: `ν` is a *local* message

Where the `𝔤` rules act on a chronicle suffix `η ⊎ {ε}`, the `𝔞` rules act on
a suffix *preceded by an explicit transition* `⟨μ, ρ ⊎ {ν}⟩`.  Since memories
only grow along a chronicle, this pins down where `ν` enters: on the `ρ` side,
i.e. `ν` is a **local** message (`ν ∈ ξ.own`).  The paper's prose says exactly
this for `Ti` ("considering a *local* message `ν`", p.36) and for `Ab` ("removes
a *local* message `ν` and decreases the initial timestamp of a *local* message
`ε`", p.36).  We therefore make `ν ∉ μ` (and, for the message that replaces it,
`ε ∉ μ`) explicit hypotheses of `ChroStep.tighten` and `ChroStep.absorb`.

⚠ For `Di` the paper says the *opposite* about `ν`: only `ε` must be local, and
"`ν` and `ν′` can appear anywhere in the trace's sequence, as long as they
appear in the same places" (ESOP conference version, Fig. 7 caption; journal
Fig. 14's caption makes the same concession for `Cn`).  `Step.dilute` accordingly
constrains only `ε`.  This asymmetry is not cosmetic: it is why `Di` can create a
local message out of nothing and so breaks the invariant `ξ.own = ∅` on which the
unit laws run; see `Isotope/Elgot/RA/Abstract.lean`.

Following the paper, the side conditions that make the *target* a trace are not
part of the rules: closure of a set `U` under a rule set only ever requires
`π ∈ U` when the rewritten pre-trace `π` is itself a trace (journal §7.2, p.28).
In particular the conditions `Ls✓`, `Ex✓`, `Cn✓` of the paper's Lemma F.1
(p.61), which *characterize* when the target is a trace, are not transcribed
here; they are needed only for Rewrite Castling, which we do not prove.

## Reconstruction: the chronicle notation `η ⊎ {ε}`

⚠ **The paper never defines `η ⊎ {ε}`.**  It is used only in the three `𝔤`
rules and, compositionally, in the proof of Deferral of Closure (journal
Appendix A, p.50).  We read it as

> `η ⊎ {ε}` is `η` with `ε` added to *every* memory (opening and closing) of
> *every* transition of `η`, with `ε` absent from all of them,

i.e. `m.map (Transition.insertMsg ε)` with `listFree ε m`.  The evidence is
journal p.33 ("the decomposition of the chronicle in the rule determines where
`ε` first appears (if at all)") and Fig. 15's caption ("since `ε` is to appear
as an environment message in the chronicle, it can appear since the opening
memory, not appear even in the closing memory, or somewhere in between").  The
disjointness is the symbol `⊎` itself, which the paper uses throughout without
comment.  **This is a reconstruction, not the paper's definition.**

Note that the reading needs no separate "`ε` is an environment message"
side condition: if `ε` occurred in the closing memory of the prefix `ξ`, then
adjacency `ξ.c ⊆ (η ⊎ {ε}).o` would already have failed, and `Chro` bakes
adjacency in.

We formalize the *relaxed* dovetailing premise `ν.vw ≤ ε.vw` of Table 2, not
the equal-view variant drawn in Figs. 13–14; see `Isotope/Elgot/RA/State.lean`.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type}

/-- The paper's nine closure rules (journal Table 2, p.30). -/
inductive Rule : Type
  /-- `St`, *stutter*. -/
  | St
  /-- `Mu`, *mumble*. -/
  | Mu
  /-- `Fw`, *forward*. -/
  | Fw
  /-- `Rw`, *rewind*. -/
  | Rw
  /-- `Ls`, *loosen*. -/
  | Ls
  /-- `Ex`, *expel*. -/
  | Ex
  /-- `Cn`, *condense*. -/
  | Cn
  /-- `Ti`, *tighten*. -/
  | Ti
  /-- `Ab`, *absorb*. -/
  | Ab
  /-- `Di`, *dilute*. -/
  | Di
  deriving DecidableEq, Repr

/-- The paper's `★`: a set of closure rules (journal §7.2, p.28). -/
abbrev RuleSet : Type := Set Rule

/-- The concrete group `𝔠 = {St, Mu, Fw, Rw}` (journal §7.4, p.34). -/
def cRules : RuleSet := {Rule.St, Rule.Mu, Rule.Fw, Rule.Rw}

/-- The generating group `𝔤 = {Ls, Ex, Cn}` (journal §7.3, p.30). -/
def gRules : RuleSet := {Rule.Ls, Rule.Ex, Rule.Cn}

/-- The Concrete model's rule set `𝔤𝔠 = 𝔤 ∪ 𝔠` (journal §7.4, p.34; the ESOP
version calls this model `M`). -/
def gcRules : RuleSet := gRules ∪ cRules

@[simp] theorem mem_cRules {x : Rule} :
    x ∈ cRules ↔ x = Rule.St ∨ x = Rule.Mu ∨ x = Rule.Fw ∨ x = Rule.Rw := by
  simp [cRules]

@[simp] theorem mem_gRules {x : Rule} :
    x ∈ gRules ↔ x = Rule.Ls ∨ x = Rule.Ex ∨ x = Rule.Cn := by
  simp [gRules]

/-- The abstract group `𝔞 = {Ti, Ab, Di}` (journal §7.5, p.35). -/
def aRules : RuleSet := {Rule.Ti, Rule.Ab, Rule.Di}

/-- The Abstract model's rule set `𝔤𝔠𝔞 = 𝔤𝔠 ∪ 𝔞` (journal §7.5, p.35). -/
def gcaRules : RuleSet := gcRules ∪ aRules

/-- `𝔤𝔠 ∪ {Ti, Ab}`: the abstract group **less dilute**.  This rule set is
*ours*, not the paper's; it is the largest set below `𝔤𝔠𝔞` for which having no
local messages is still a rewriting invariant, hence the largest one for which
the unit laws of `Isotope/Elgot/RA/Monad.lean` are proved.  See
`Isotope/Elgot/RA/Abstract.lean`. -/
def gcTiAbRules : RuleSet := gcRules ∪ {Rule.Ti, Rule.Ab}

@[simp] theorem mem_gcRules {x : Rule} :
    x ∈ gcRules ↔ x = Rule.St ∨ x = Rule.Mu ∨ x = Rule.Fw ∨ x = Rule.Rw ∨
      x = Rule.Ls ∨ x = Rule.Ex ∨ x = Rule.Cn := by
  simp only [gcRules, Set.mem_union, mem_gRules, mem_cRules]; tauto

@[simp] theorem mem_aRules {x : Rule} :
    x ∈ aRules ↔ x = Rule.Ti ∨ x = Rule.Ab ∨ x = Rule.Di := by
  simp [aRules]

@[simp] theorem mem_gcTiAbRules {x : Rule} : x ∈ gcTiAbRules ↔ x ≠ Rule.Di := by
  simp only [gcTiAbRules, Set.mem_union, mem_gcRules, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  cases x <;> simp

@[simp] theorem mem_gcaRules {x : Rule} : x ∈ gcaRules ↔ True := by
  simp only [gcaRules, Set.mem_union, mem_gcRules, mem_aRules, iff_true]
  cases x <;> simp

theorem cRules_subset_gcRules : cRules ⊆ gcRules := fun _ h ↦ Or.inr h

theorem gRules_subset_gcRules : gRules ⊆ gcRules := fun _ h ↦ Or.inl h

theorem gcRules_subset_gcTiAbRules : gcRules ⊆ gcTiAbRules := fun _ h ↦ Or.inl h

theorem cRules_subset_gcTiAbRules : cRules ⊆ gcTiAbRules :=
  cRules_subset_gcRules.trans gcRules_subset_gcTiAbRules

theorem gRules_subset_gcTiAbRules : gRules ⊆ gcTiAbRules :=
  gRules_subset_gcRules.trans gcRules_subset_gcTiAbRules

theorem gcTiAbRules_subset_gcaRules : gcTiAbRules ⊆ gcaRules := fun _ _ ↦ by simp

theorem gcRules_subset_gcaRules : gcRules ⊆ gcaRules := fun _ _ ↦ by simp

theorem aRules_subset_gcaRules : aRules ⊆ gcaRules := fun _ _ ↦ by simp

theorem cRules_subset_gcaRules : cRules ⊆ gcaRules := fun _ _ ↦ by simp

theorem gRules_subset_gcaRules : gRules ⊆ gcaRules := fun _ _ ↦ by simp

/-- `ν` occurs in no memory of `l`: the disjointness carried by the paper's
`⊎` in `η ⊎ {ν}`. -/
def listFree (ν : Msg Loc Val) (l : List (Transition Loc Val)) : Prop :=
  ∀ T ∈ l, ν ∉ T.opening ∧ ν ∉ T.closing

theorem listFree.mono {ν : Msg Loc Val} {l m : List (Transition Loc Val)}
    (h : listFree ν m) (hsub : ∀ T ∈ l, T ∈ m) : listFree ν l :=
  fun T hT ↦ h T (hsub T hT)

/-- The rewrite rules that act on the chronicle alone: `St`, `Mu` (group `𝔠`)
and `Ls`, `Ex` (group `𝔤`).  Only `Cn` acts on the whole pre-trace. -/
inductive ChroStep : Rule → Chro Loc Val → Chro Loc Val → Prop
  /-- `Stutter`: insert a transition `⟨μ,μ⟩` anywhere in the chronicle. -/
  | stutter (c₁ c₂ : Chro Loc Val) (l r : List (Transition Loc Val)) (μ : Memory Loc Val)
      (h₁ : c₁.toList = l ++ r) (h₂ : c₂.toList = l ++ ⟨μ, μ⟩ :: r) :
      ChroStep Rule.St c₁ c₂
  /-- `Mumble`: merge two adjacent transitions `⟨μ,ρ⟩⟨ρ,θ⟩` into `⟨μ,θ⟩`. -/
  | mumble (c₁ c₂ : Chro Loc Val) (l r : List (Transition Loc Val))
      (μ ρ θ : Memory Loc Val)
      (h₁ : c₁.toList = l ++ ⟨μ, ρ⟩ :: ⟨ρ, θ⟩ :: r)
      (h₂ : c₂.toList = l ++ ⟨μ, θ⟩ :: r) : ChroStep Rule.Mu c₁ c₂
  /-- `Loosen` (journal §7.3, p.31): replace the environment message `ε` by a
  weaker `ν ≤vw ε` in every memory of a chronicle suffix. -/
  | loosen (c₁ c₂ : Chro Loc Val) (l m : List (Transition Loc Val)) (ν ε : Msg Loc Val)
      (hle : Msg.LeVw ν ε) (hfε : listFree ε m) (hfν : listFree ν m)
      (h₁ : c₁.toList = l ++ m.map (Transition.insertMsg ε))
      (h₂ : c₂.toList = l ++ m.map (Transition.insertMsg ν)) :
      ChroStep Rule.Ls c₁ c₂
  /-- `Expel` (journal §7.3, pp.31–32): split the environment message
  `ε[i↦ν.i]` into two dovetailing messages `ν ⤙ ε` occupying the same
  segment. -/
  | expel (c₁ c₂ : Chro Loc Val) (l m : List (Transition Loc Val)) (ν ε : Msg Loc Val)
      (hdt : Msg.Dovetail ν ε)
      (hfs : listFree (ε.setI ν.i hdt.i_lt_t) m)
      (hfν : listFree ν m) (hfε : listFree ε m)
      (h₁ : c₁.toList = l ++ m.map (Transition.insertMsg (ε.setI ν.i hdt.i_lt_t)))
      (h₂ : c₂.toList = l ++ m.map (fun T ↦ (T.insertMsg ε).insertMsg ν)) :
      ChroStep Rule.Ex c₁ c₂
  /-- `Tighten` (journal §7.5, p.36): replace the *local* message `ν` by a
  stronger `ν ≤vw ε` in the transition that introduces it and in every later
  memory.  The hypotheses `hνμ`, `hεμ` are our reading of the paper's
  `⟨μ, ρ ⊎ {ν}⟩`: the message enters on the closing side, i.e. it is local. -/
  | tighten (c₁ c₂ : Chro Loc Val) (l m : List (Transition Loc Val))
      (μ ρ : Memory Loc Val) (ν ε : Msg Loc Val)
      (hle : Msg.LeVw ν ε)
      (hνμ : ν ∉ μ) (hνρ : ν ∉ ρ) (hεμ : ε ∉ μ) (hερ : ε ∉ ρ)
      (hfν : listFree ν m) (hfε : listFree ε m)
      (h₁ : c₁.toList = l ++ ⟨μ, insert ν ρ⟩ :: m.map (Transition.insertMsg ν))
      (h₂ : c₂.toList = l ++ ⟨μ, insert ε ρ⟩ :: m.map (Transition.insertMsg ε)) :
      ChroStep Rule.Ti c₁ c₂
  /-- `Absorb` (journal §7.5, pp.36–37): merge the dovetailing *local* pair
  `ν ⤙ ε` into the single message `ε[i↦ν.i]`, which covers both segments. -/
  | absorb (c₁ c₂ : Chro Loc Val) (l m : List (Transition Loc Val))
      (μ ρ : Memory Loc Val) (ν ε : Msg Loc Val)
      (hdt : Msg.Dovetail ν ε)
      (hνμ : ν ∉ μ) (hνρ : ν ∉ ρ) (hεμ : ε ∉ μ) (hερ : ε ∉ ρ)
      (hsμ : ε.setI ν.i hdt.i_lt_t ∉ μ) (hsρ : ε.setI ν.i hdt.i_lt_t ∉ ρ)
      (hfν : listFree ν m) (hfε : listFree ε m)
      (hfs : listFree (ε.setI ν.i hdt.i_lt_t) m)
      (h₁ : c₁.toList =
        l ++ ⟨μ, insert ν (insert ε ρ)⟩ :: m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
      (h₂ : c₂.toList =
        l ++ ⟨μ, insert (ε.setI ν.i hdt.i_lt_t) ρ⟩ ::
          m.map (Transition.insertMsg (ε.setI ν.i hdt.i_lt_t))) :
      ChroStep Rule.Ab c₁ c₂

namespace ChroStep

/-- Stutter and mumble can only grow the closing memory.  This fails for the
`𝔤` rules, which *replace* messages in the closing memory. -/
theorem c_sub {x : Rule} {c₁ c₂ : Chro Loc Val} (hx : x ∈ cRules) (h : ChroStep x c₁ c₂) :
    c₁.c ⊆ c₂.c := by
  cases h with
  | stutter _ _ l r μ h₁ h₂ =>
      cases r with
      | nil =>
          have hne : l ≠ [] := by
            intro hl
            exact c₁.toList_ne_nil (by rw [h₁, hl]; rfl)
          have hch : List.IsChain Adj c₂.toList := c₂.chain_toList
          rw [h₂] at hch
          have := chain'_listC_sub l ⟨μ, μ⟩ [] hch hne
          simp only [Chro.c, h₁, h₂, List.append_nil, listC_append, listC_singleton]
          exact this
      | cons S r =>
          simp only [Chro.c, h₁, h₂, listC_append, listC_cons_cons, subset_refl]
  | mumble _ _ l r μ ρ θ h₁ h₂ =>
      cases r with
      | nil =>
          simp only [Chro.c, h₁, h₂, listC_append, listC_cons_cons, listC_singleton, subset_refl]
      | cons S r =>
          simp only [Chro.c, h₁, h₂, listC_append, listC_cons_cons, subset_refl]
  | loosen => simp at hx
  | expel => simp at hx
  | tighten => simp at hx
  | absorb => simp at hx

/-- Stutter and mumble can only shrink the opening memory.  This fails for the
`𝔤` rules. -/
theorem o_sub {x : Rule} {c₁ c₂ : Chro Loc Val} (hx : x ∈ cRules) (h : ChroStep x c₁ c₂) :
    c₂.o ⊆ c₁.o := by
  cases h with
  | stutter _ _ l r μ h₁ h₂ =>
      cases l with
      | nil =>
          cases r with
          | nil => exact absurd (by rw [h₁]; rfl) c₁.toList_ne_nil
          | cons S r =>
              have hch : List.IsChain Adj c₂.toList := c₂.chain_toList
              rw [h₂, List.nil_append] at hch
              have hadj : Adj (⟨μ, μ⟩ : Transition Loc Val) S :=
                (List.isChain_cons_cons.mp hch).1
              simp only [Chro.o, h₁, h₂, List.nil_append, listO_cons]
              exact hadj
      | cons T l => simp only [Chro.o, h₁, h₂, List.cons_append, listO_cons, subset_refl]
  | mumble _ _ l r μ ρ θ h₁ h₂ =>
      cases l with
      | nil => simp only [Chro.o, h₁, h₂, List.nil_append, listO_cons, subset_refl]
      | cons T l => simp only [Chro.o, h₁, h₂, List.cons_append, listO_cons, subset_refl]
  | loosen => simp at hx
  | expel => simp at hx
  | tighten => simp at hx
  | absorb => simp at hx

/-- Rewriting the left operand of a concatenation, for the `𝔠` rules. -/
theorem appendLeft {x : Rule} {c₁ c₂ d : Chro Loc Val} (hx : x ∈ cRules)
    (h : ChroStep x c₁ c₂) (h₁ : c₁.c ⊆ d.o) (h₂ : c₂.c ⊆ d.o) :
    ChroStep x (c₁.append d h₁) (c₂.append d h₂) := by
  cases h with
  | stutter _ _ l r μ e₁ e₂ =>
      refine ChroStep.stutter _ _ l (r ++ d.toList) μ ?_ ?_
      · rw [Chro.append_toList, e₁, List.append_assoc]
      · rw [Chro.append_toList, e₂, List.append_assoc, List.cons_append]
  | mumble _ _ l r μ ρ θ e₁ e₂ =>
      refine ChroStep.mumble _ _ l (r ++ d.toList) μ ρ θ ?_ ?_
      · rw [Chro.append_toList, e₁, List.append_assoc, List.cons_append, List.cons_append]
      · rw [Chro.append_toList, e₂, List.append_assoc, List.cons_append]
  | loosen => simp at hx
  | expel => simp at hx
  | tighten => simp at hx
  | absorb => simp at hx

/-- Rewriting the right operand of a concatenation, for the `𝔠` rules. -/
theorem appendRight {x : Rule} {c₁ c₂ d : Chro Loc Val} (hx : x ∈ cRules)
    (h : ChroStep x c₁ c₂) (h₁ : d.c ⊆ c₁.o) (h₂ : d.c ⊆ c₂.o) :
    ChroStep x (d.append c₁ h₁) (d.append c₂ h₂) := by
  cases h with
  | stutter _ _ l r μ e₁ e₂ =>
      refine ChroStep.stutter _ _ (d.toList ++ l) r μ ?_ ?_
      · rw [Chro.append_toList, e₁, List.append_assoc]
      · rw [Chro.append_toList, e₂, List.append_assoc]
  | mumble _ _ l r μ ρ θ e₁ e₂ =>
      refine ChroStep.mumble _ _ (d.toList ++ l) r μ ρ θ ?_ ?_
      · rw [Chro.append_toList, e₁, List.append_assoc]
      · rw [Chro.append_toList, e₂, List.append_assoc]
  | loosen => simp at hx
  | expel => simp at hx
  | tighten => simp at hx
  | absorb => simp at hx

/-- The chronicle rewrites preserve the number of transitions, except for
`Mumble`, which shortens it by one.  In particular the three `𝔤` rules preserve
it — the reason the paper's counterexample at journal p.30 works. -/
theorem length_eq {x : Rule} {c₁ c₂ : Chro Loc Val} (hx : x ∈ gRules)
    (h : ChroStep x c₁ c₂) : c₁.toList.length = c₂.toList.length := by
  cases h with
  | stutter => simp at hx
  | mumble => simp at hx
  | loosen _ _ l m ν ε _ _ _ h₁ h₂ => rw [h₁, h₂]; simp
  | expel _ _ l m ν ε _ _ _ _ h₁ h₂ => rw [h₁, h₂]; simp
  | tighten => simp at hx
  | absorb => simp at hx

end ChroStep

/-- One `★`-rewrite of a pre-trace, for an arbitrary rule set `★ = R`.  Each
constructor carries the hypothesis that its rule belongs to `R`, so that
`Step R` is literally the paper's `─★→`. -/
inductive Step (R : RuleSet) {A : Type u} : PreTrace Loc Val A → PreTrace Loc Val A → Prop
  /-- `Stutter`, `Mumble`, `Loosen` or `Expel`, acting on the chronicle. -/
  | chro {x : Rule} (hx : x ∈ R) {α ω : View Loc} {r : A} {c₁ c₂ : Chro Loc Val}
      (h : ChroStep x c₁ c₂) : Step R ⟨α, c₁, ω, r⟩ ⟨α, c₂, ω, r⟩
  /-- `Forward`: weaken the final view. -/
  | forward (hx : Rule.Fw ∈ R) {α κ ω : View Loc} {r : A} {c : Chro Loc Val}
      (h : κ ≤ ω) : Step R ⟨α, c, κ, r⟩ ⟨α, c, ω, r⟩
  /-- `Rewind`: strengthen the initial view. -/
  | rewind (hx : Rule.Rw ∈ R) {α κ ω : View Loc} {r : A} {c : Chro Loc Val}
      (h : α ≤ κ) : Step R ⟨κ, c, ω, r⟩ ⟨α, c, ω, r⟩
  /-- `Condense` (journal §7.3, pp.32–33): merge the dovetailing same-value
  environment pair `ν ⤙= ε` into `ν[↑ε]`, and pull the *whole pre-trace* along
  `ε`.  This is the only rule of the paper that is not local to the
  chronicle. -/
  | condense (hx : Rule.Cn ∈ R) {α ω : View Loc} {r : A} {c₁ c₂ : Chro Loc Val}
      (l m : List (Transition Loc Val)) (ν ε : Msg Loc Val)
      (hde : Msg.DovetailEq ν ε) (hfν : listFree ν m) (hfε : listFree ε m)
      (h₁ : c₁.toList = l ++ m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
      (h₂ : c₂.toList = (l ++ m.map (Transition.insertMsg ν)).map (Transition.pull ε)) :
      Step R ⟨α, c₁, ω, r⟩ ⟨View.pull ε α, c₂, View.pull ε ω, r⟩
  /-- `Dilute` (journal §7.5, p.37): the mirror image of `Condense`.  A message
  `ν[↑ε]` splits into `ν` together with a *local* message `ν ⤙= ε` filling out
  the rest of its segment; the source, not the target, is the pulled pre-trace.
  Only `ε` is required to be local (journal Fig. 14, ESOP conference Fig. 7). -/
  | dilute (hx : Rule.Di ∈ R) {α ω : View Loc} {r : A} {c₁ c₂ : Chro Loc Val}
      (l m : List (Transition Loc Val)) (μ ρ : Memory Loc Val) (ν ε : Msg Loc Val)
      (hde : Msg.DovetailEq ν ε)
      (hεμ : ε ∉ μ) (hερ : ε ∉ ρ) (hνρ : ν ∉ ρ)
      (hfν : listFree ν m) (hfε : listFree ε m)
      (h₁ : c₁.toList =
        (l ++ ⟨μ, insert ν ρ⟩ :: m.map (Transition.insertMsg ν)).map (Transition.pull ε))
      (h₂ : c₂.toList =
        l ++ ⟨μ, insert ν (insert ε ρ)⟩ :: m.map (fun T ↦ (T.insertMsg ε).insertMsg ν)) :
      Step R ⟨View.pull ε α, c₁, View.pull ε ω, r⟩ ⟨α, c₂, ω, r⟩

/-- Enlarging the rule set only adds rewrites: the paper's `G X ⊇ C X ⊇ A X`
(journal §8.2, p.41) rests on nothing more than this. -/
theorem Step.mono {R R' : RuleSet} (hR : R ⊆ R') {A : Type u}
    {τ π : PreTrace Loc Val A} (h : Step R τ π) : Step R' τ π := by
  cases h with
  | chro hx hc => exact Step.chro (hR hx) hc
  | forward hx h => exact Step.forward (hR hx) h
  | rewind hx h => exact Step.rewind (hR hx) h
  | condense hx l m ν ε hde hfν hfε h₁ h₂ =>
      exact Step.condense (hR hx) l m ν ε hde hfν hfε h₁ h₂
  | dilute hx l m μ ρ ν ε hde hεμ hερ hνρ hfν hfε h₁ h₂ =>
      exact Step.dilute (hR hx) l m μ ρ ν ε hde hεμ hερ hνρ hfν hfε h₁ h₂

/-- A rewrite step whose target is again a trace: the only steps that a
`★`-closed set of traces is required to follow (journal §7.2, p.28). -/
def TStep (R : RuleSet) {A : Type u} (τ π : PreTrace Loc Val A) : Prop :=
  Step R τ π ∧ IsTrace π

theorem TStep.mono {R R' : RuleSet} (hR : R ⊆ R') {A : Type u}
    {τ π : PreTrace Loc Val A} (h : TStep R τ π) : TStep R' τ π :=
  ⟨h.1.mono hR, h.2⟩

/-- Reachability under `TStep R`. -/
def Refines (R : RuleSet) {A : Type u} (τ π : PreTrace Loc Val A) : Prop :=
  Relation.ReflTransGen (TStep R) τ π

variable {R : RuleSet} {A : Type u}

theorem Refines.refl (τ : PreTrace Loc Val A) : Refines R τ τ :=
  Relation.ReflTransGen.refl

theorem Refines.trans {τ π ζ : PreTrace Loc Val A}
    (h₁ : Refines R τ π) (h₂ : Refines R π ζ) : Refines R τ ζ :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Refines.single {τ π : PreTrace Loc Val A} (h : TStep R τ π) :
    Refines R τ π := Relation.ReflTransGen.single h

theorem Refines.mono {R' : RuleSet} (hR : R ⊆ R') {τ π : PreTrace Loc Val A}
    (h : Refines R τ π) : Refines R' τ π := by
  induction h with
  | refl => exact Refines.refl _
  | tail _ hstep ih => exact ih.tail (hstep.mono hR)

/-- Concatenation of pre-traces at a seam. -/
def PreTrace.seam {A B : Type u} (τ : PreTrace Loc Val A) (υ : PreTrace Loc Val B)
    (h : τ.ch.c ⊆ υ.ch.o) : PreTrace Loc Val B :=
  ⟨τ.ivw, τ.ch.append υ.ch h, υ.fvw, υ.ret⟩

@[simp] theorem PreTrace.seam_ivw {A B : Type u} (τ : PreTrace Loc Val A)
    (υ : PreTrace Loc Val B) (h : τ.ch.c ⊆ υ.ch.o) : (τ.seam υ h).ivw = τ.ivw := rfl

@[simp] theorem PreTrace.seam_fvw {A B : Type u} (τ : PreTrace Loc Val A)
    (υ : PreTrace Loc Val B) (h : τ.ch.c ⊆ υ.ch.o) : (τ.seam υ h).fvw = υ.fvw := rfl

@[simp] theorem PreTrace.seam_ret {A B : Type u} (τ : PreTrace Loc Val A)
    (υ : PreTrace Loc Val B) (h : τ.ch.c ⊆ υ.ch.o) : (τ.seam υ h).ret = υ.ret := rfl

@[simp] theorem PreTrace.seam_ch {A B : Type u} (τ : PreTrace Loc Val A)
    (υ : PreTrace Loc Val B) (h : τ.ch.c ⊆ υ.ch.o) :
    (τ.seam υ h).ch = τ.ch.append υ.ch h := rfl

end Isotope.Elgot.RA
