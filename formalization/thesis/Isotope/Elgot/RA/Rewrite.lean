import Isotope.Elgot.RA.Trace

/-!
# The concrete rewrite rules `𝔠`

Transcribed from Dvir, Kammar and Lahav (`release-acquire`), Table 1 of the ESOP
version / Table 2 of the TOPLAS journal version, group `𝔠`:

```
Stutter  (St)   α ξη ω              →  α ξ ⟨μ,μ⟩ η ω
Mumble   (Mu)   α ξ ⟨μ,ρ⟩⟨ρ,θ⟩ η ω  →  α ξ ⟨μ,θ⟩ η ω
Forward  (Fw)   α ξ κ ◁ r           →  α ξ ω ◁ r        if κ ⊑ ω
Rewind   (Rw)   κ ξ ω ◁ r           →  α ξ ω ◁ r        if α ⊑ κ
```

Following the paper, the side conditions that make the *target* a trace (`μ`
well-formed, `α ↠ ξ.o`, `ω ↠ ξ.c`) are not part of the rules: closure of a set
`U` under a rule set only ever requires `π ∈ U` when the rewritten pre-trace `π`
is itself a trace.

We do **not** formalize the groups `𝔤 = {Ls, Ex, Cn}` and `𝔞 = {Ti, Ab, Di}`;
see the honest boundary in `Isotope/Elgot/RA.lean`.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type}

/-- Stutter and mumble, as rewrites of chronicles. -/
inductive ChroStep : Chro Loc Val → Chro Loc Val → Prop
  /-- `Stutter`: insert a transition `⟨μ,μ⟩` anywhere in the chronicle. -/
  | stutter (c₁ c₂ : Chro Loc Val) (l r : List (Transition Loc Val)) (μ : Memory Loc Val)
      (h₁ : c₁.toList = l ++ r) (h₂ : c₂.toList = l ++ ⟨μ, μ⟩ :: r) : ChroStep c₁ c₂
  /-- `Mumble`: merge two adjacent transitions `⟨μ,ρ⟩⟨ρ,θ⟩` into `⟨μ,θ⟩`. -/
  | mumble (c₁ c₂ : Chro Loc Val) (l r : List (Transition Loc Val))
      (μ ρ θ : Memory Loc Val)
      (h₁ : c₁.toList = l ++ ⟨μ, ρ⟩ :: ⟨ρ, θ⟩ :: r)
      (h₂ : c₂.toList = l ++ ⟨μ, θ⟩ :: r) : ChroStep c₁ c₂

namespace ChroStep

/-- Stutter and mumble can only grow the closing memory. -/
theorem c_sub {c₁ c₂ : Chro Loc Val} (h : ChroStep c₁ c₂) : c₁.c ⊆ c₂.c := by
  cases h with
  | stutter l r μ h₁ h₂ =>
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
  | mumble l r μ ρ θ h₁ h₂ =>
      cases r with
      | nil =>
          simp only [Chro.c, h₁, h₂, listC_append, listC_cons_cons, listC_singleton, subset_refl]
      | cons S r =>
          simp only [Chro.c, h₁, h₂, listC_append, listC_cons_cons, subset_refl]

/-- Stutter and mumble can only shrink the opening memory. -/
theorem o_sub {c₁ c₂ : Chro Loc Val} (h : ChroStep c₁ c₂) : c₂.o ⊆ c₁.o := by
  cases h with
  | stutter l r μ h₁ h₂ =>
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
  | mumble l r μ ρ θ h₁ h₂ =>
      cases l with
      | nil => simp only [Chro.o, h₁, h₂, List.nil_append, listO_cons, subset_refl]
      | cons T l => simp only [Chro.o, h₁, h₂, List.cons_append, listO_cons, subset_refl]

/-- Rewriting the left operand of a concatenation. -/
theorem appendLeft {c₁ c₂ d : Chro Loc Val} (h : ChroStep c₁ c₂)
    (h₁ : c₁.c ⊆ d.o) (h₂ : c₂.c ⊆ d.o) :
    ChroStep (c₁.append d h₁) (c₂.append d h₂) := by
  cases h with
  | stutter l r μ e₁ e₂ =>
      refine ChroStep.stutter _ _ l (r ++ d.toList) μ ?_ ?_
      · rw [Chro.append_toList, e₁, List.append_assoc]
      · rw [Chro.append_toList, e₂, List.append_assoc, List.cons_append]
  | mumble l r μ ρ θ e₁ e₂ =>
      refine ChroStep.mumble _ _ l (r ++ d.toList) μ ρ θ ?_ ?_
      · rw [Chro.append_toList, e₁, List.append_assoc, List.cons_append, List.cons_append]
      · rw [Chro.append_toList, e₂, List.append_assoc, List.cons_append]

/-- Rewriting the right operand of a concatenation. -/
theorem appendRight {c₁ c₂ d : Chro Loc Val} (h : ChroStep c₁ c₂)
    (h₁ : d.c ⊆ c₁.o) (h₂ : d.c ⊆ c₂.o) :
    ChroStep (d.append c₁ h₁) (d.append c₂ h₂) := by
  cases h with
  | stutter l r μ e₁ e₂ =>
      refine ChroStep.stutter _ _ (d.toList ++ l) r μ ?_ ?_
      · rw [Chro.append_toList, e₁, List.append_assoc]
      · rw [Chro.append_toList, e₂, List.append_assoc]
  | mumble l r μ ρ θ e₁ e₂ =>
      refine ChroStep.mumble _ _ (d.toList ++ l) r μ ρ θ ?_ ?_
      · rw [Chro.append_toList, e₁, List.append_assoc]
      · rw [Chro.append_toList, e₂, List.append_assoc]

end ChroStep

/-- One `𝔠`-rewrite of a pre-trace: stutter or mumble on the chronicle,
`Forward` on the final view, `Rewind` on the initial view. -/
inductive Step {A : Type u} : PreTrace Loc Val A → PreTrace Loc Val A → Prop
  /-- `Stutter`/`Mumble`. -/
  | chro {α ω : View Loc} {r : A} {c₁ c₂ : Chro Loc Val} (h : ChroStep c₁ c₂) :
      Step ⟨α, c₁, ω, r⟩ ⟨α, c₂, ω, r⟩
  /-- `Forward`: weaken the final view. -/
  | forward {α κ ω : View Loc} {r : A} {c : Chro Loc Val} (h : κ ≤ ω) :
      Step ⟨α, c, κ, r⟩ ⟨α, c, ω, r⟩
  /-- `Rewind`: strengthen the initial view. -/
  | rewind {α κ ω : View Loc} {r : A} {c : Chro Loc Val} (h : α ≤ κ) :
      Step ⟨κ, c, ω, r⟩ ⟨α, c, ω, r⟩

/-- A rewrite step whose target is again a trace: the only steps that a
`𝔠`-closed set of traces is required to follow. -/
def TStep {A : Type u} (τ π : PreTrace Loc Val A) : Prop := Step τ π ∧ IsTrace π

/-- Reachability under `TStep`. -/
def Refines {A : Type u} (τ π : PreTrace Loc Val A) : Prop :=
  Relation.ReflTransGen TStep τ π

theorem Refines.refl {A : Type u} (τ : PreTrace Loc Val A) : Refines τ τ :=
  Relation.ReflTransGen.refl

theorem Refines.trans {A : Type u} {τ π ζ : PreTrace Loc Val A}
    (h₁ : Refines τ π) (h₂ : Refines π ζ) : Refines τ ζ :=
  Relation.ReflTransGen.trans h₁ h₂

theorem Refines.single {A : Type u} {τ π : PreTrace Loc Val A} (h : TStep τ π) :
    Refines τ π := Relation.ReflTransGen.single h

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
