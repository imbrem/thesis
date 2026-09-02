import Isotope.Elgot.RA.State
import Mathlib.Data.List.Chain

/-!
# Transitions, chronicles, and traces

Transcribed from Dvir, Kammar and Lahav (`release-acquire`), §6.1 of the ESOP
full version / §7.2 of the TOPLAS journal version:

* a *transition* is a pair `⟨μ, ρ⟩` of memories with `μ ⊆ ρ`;
* a *chronicle* `ξ = ⟨μ₁,ρ₁⟩ … ⟨μₙ,ρₙ⟩` is a sequence of transitions with
  `ρⱼ ⊆ μⱼ₊₁`, with opening `ξ.o := μ₁`, closing `ξ.c := ρₙ`, and local
  messages `ξ.own := ⋃ᵢ (ρᵢ \ μᵢ)`;
* an `X`-*pre-trace* is `α ξ ω ◁ r` with `ξ` **non-empty**;
* it is an `X`-*trace* when every transition consists of well-formed memories,
  `ξ.o ↞ α ⊑ ω ↠ ξ.c`, and every local message satisfies
  `α ⊑ ν.vw ⊑ ω` and `α ν.lc < ν.t`.

Since pre-traces carry non-empty chronicles, `Chro` is represented as a first
transition together with a (possibly empty) tail, rather than as a list with a
side condition; the `Transition`-level condition `μ ⊆ ρ` is folded into
`Transition.WF`, which is exactly where the paper's trace condition uses it.
-/

namespace Isotope.Elgot.RA

variable {Loc Val : Type}

/-- A transition `⟨μ, ρ⟩`. -/
structure Transition (Loc Val : Type) where
  /-- The opening memory `μ`. -/
  opening : Memory Loc Val
  /-- The closing memory `ρ`. -/
  closing : Memory Loc Val

/-- A transition is well-formed when both memories are and `μ ⊆ ρ`. -/
structure Transition.WF (T : Transition Loc Val) : Prop where
  /-- The opening memory is well-formed. -/
  opening : WellFormed T.opening
  /-- The closing memory is well-formed. -/
  closing : WellFormed T.closing
  /-- The paper's condition on transitions. -/
  sub : T.opening ⊆ T.closing

/-- The messages contributed by a transition: `ρ \ μ`. -/
def Transition.own (T : Transition Loc Val) : Memory Loc Val := T.closing \ T.opening

/-- Chronicle adjacency: `ρⱼ ⊆ μⱼ₊₁`. -/
def Adj (S T : Transition Loc Val) : Prop := S.closing ⊆ T.opening

/-- The opening memory of a list of transitions (junk on the empty list). -/
def listO : List (Transition Loc Val) → Memory Loc Val
  | [] => ∅
  | T :: _ => T.opening

/-- The closing memory of a list of transitions (junk on the empty list). -/
def listC : List (Transition Loc Val) → Memory Loc Val
  | [] => ∅
  | [T] => T.closing
  | _ :: l => listC l

@[simp] theorem listO_cons (T : Transition Loc Val) (l : List (Transition Loc Val)) :
    listO (T :: l) = T.opening := rfl

@[simp] theorem listC_singleton (T : Transition Loc Val) : listC [T] = T.closing := rfl

@[simp] theorem listC_cons_cons (T S : Transition Loc Val)
    (l : List (Transition Loc Val)) : listC (T :: S :: l) = listC (S :: l) := rfl

theorem listC_append (l : List (Transition Loc Val)) (S : Transition Loc Val)
    (r : List (Transition Loc Val)) : listC (l ++ S :: r) = listC (S :: r) := by
  induction l with
  | nil => rfl
  | cons T l ih =>
      cases l with
      | nil => rfl
      | cons U l => simpa using ih

/-- Every non-empty list of transitions ends in a transition whose closing memory
is the list's. -/
theorem listC_concat (l : List (Transition Loc Val)) (h : l ≠ []) :
    ∃ (l' : List (Transition Loc Val)) (T : Transition Loc Val),
      l = l' ++ [T] ∧ listC l = T.closing := by
  rcases List.eq_nil_or_concat' l with rfl | ⟨L, T, rfl⟩
  · exact absurd rfl h
  · exact ⟨L, T, rfl, by rw [listC_append, listC_singleton]⟩

theorem listC_mem (l : List (Transition Loc Val)) (h : l ≠ []) :
    ∃ T ∈ l, listC l = T.closing := by
  obtain ⟨l', T, rfl, hc⟩ := listC_concat l h
  exact ⟨T, by simp, hc⟩

/-- In an adjacent list `l ++ S :: r` with `l` non-empty, the closing memory of
`l` is contained in the opening memory of `S`. -/
theorem chain'_listC_sub : ∀ (l : List (Transition Loc Val)) (S : Transition Loc Val)
    (r : List (Transition Loc Val)), List.IsChain Adj (l ++ S :: r) → l ≠ [] →
    listC l ⊆ S.opening
  | [], _, _, _, h => absurd rfl h
  | [T], S, r, hc, _ => by
      simpa using (List.isChain_cons_cons.mp hc).1
  | T :: U :: l, S, r, hc, _ => by
      have := chain'_listC_sub (U :: l) S r (List.isChain_cons_cons.mp hc).2 (by simp)
      simpa using this

/-- The local messages of a list of transitions. -/
def listOwn (l : List (Transition Loc Val)) : Memory Loc Val := {ν | ∃ T ∈ l, ν ∈ T.own}

@[simp] theorem listOwn_nil : listOwn ([] : List (Transition Loc Val)) = ∅ := by
  ext ν; simp [listOwn]

@[simp] theorem listOwn_cons (T : Transition Loc Val) (l : List (Transition Loc Val)) :
    listOwn (T :: l) = T.own ∪ listOwn l := by
  ext ν; simp [listOwn, or_and_right, exists_or]

theorem listOwn_append (l r : List (Transition Loc Val)) :
    listOwn (l ++ r) = listOwn l ∪ listOwn r := by
  induction l with
  | nil => simp
  | cons T l ih => simp [ih, Set.union_assoc]

/-- A chronicle: a non-empty sequence of adjacent transitions. -/
structure Chro (Loc Val : Type) where
  /-- The first transition. -/
  first : Transition Loc Val
  /-- The remaining transitions. -/
  rest : List (Transition Loc Val)
  /-- Adjacency `ρⱼ ⊆ μⱼ₊₁`. -/
  chain : List.IsChain Adj (first :: rest)

namespace Chro

/-- The transitions of a chronicle, as a list. -/
def toList (ξ : Chro Loc Val) : List (Transition Loc Val) := ξ.first :: ξ.rest

theorem toList_ne_nil (ξ : Chro Loc Val) : ξ.toList ≠ [] := by simp [toList]

theorem chain_toList (ξ : Chro Loc Val) : List.IsChain Adj ξ.toList := ξ.chain

/-- The opening memory `ξ.o := μ₁`. -/
def o (ξ : Chro Loc Val) : Memory Loc Val := listO ξ.toList

/-- The closing memory `ξ.c := ρₙ`. -/
def c (ξ : Chro Loc Val) : Memory Loc Val := listC ξ.toList

/-- The local messages `ξ.own := ⋃ᵢ (ρᵢ \ μᵢ)`. -/
def own (ξ : Chro Loc Val) : Memory Loc Val := listOwn ξ.toList

theorem own_eq_listOwn (ξ : Chro Loc Val) : ξ.own = listOwn ξ.toList := rfl

@[ext] theorem ext {ξ η : Chro Loc Val} (hf : ξ.first = η.first)
    (hr : ξ.rest = η.rest) : ξ = η := by
  cases ξ; cases η; cases hf; cases hr; rfl

theorem ext_toList {ξ η : Chro Loc Val} (h : ξ.toList = η.toList) : ξ = η := by
  cases ξ; cases η; simp only [toList, List.cons.injEq] at h; exact ext h.1 h.2

theorem first_mem (ξ : Chro Loc Val) : ξ.first ∈ ξ.toList := by simp [toList]

/-- The one-transition chronicle. -/
def single (T : Transition Loc Val) : Chro Loc Val where
  first := T
  rest := []
  chain := List.isChain_singleton T

@[simp] theorem single_toList (T : Transition Loc Val) : (single T).toList = [T] := rfl

@[simp] theorem single_o (T : Transition Loc Val) : (single T).o = T.opening := rfl

@[simp] theorem single_c (T : Transition Loc Val) : (single T).c = T.closing := rfl

@[simp] theorem single_own (T : Transition Loc Val) : (single T).own = T.own := by
  simp [own]

end Chro

/-- The closing memory of a non-empty list is that of its last transition. -/
theorem listC_getLast? : ∀ (l : List (Transition Loc Val)) (T : Transition Loc Val),
    l.getLast? = some T → listC l = T.closing
  | [], _, h => by simp at h
  | [S], T, h => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      subst h; rfl
  | S :: U :: l, T, h => by
      rw [listC_cons_cons]
      exact listC_getLast? (U :: l) T (by simpa using h)

namespace Chro

/-- Concatenation of chronicles, defined when the closing memory of the first is
contained in the opening memory of the second. -/
def append (ξ η : Chro Loc Val) (h : ξ.c ⊆ η.o) : Chro Loc Val where
  first := ξ.first
  rest := ξ.rest ++ η.first :: η.rest
  chain := by
    have hlist : ξ.first :: (ξ.rest ++ η.first :: η.rest) = ξ.toList ++ η.toList := rfl
    rw [hlist]
    refine List.isChain_append.2 ⟨ξ.chain, η.chain, ?_⟩
    intro x hx y hy
    rw [Option.mem_def] at hx hy
    have hx' : listC ξ.toList = x.closing := listC_getLast? _ _ hx
    have hy' : y = η.first := by
      simp only [toList, List.head?_cons, Option.some.injEq] at hy
      exact hy.symm
    subst hy'
    change x.closing ⊆ η.first.opening
    rw [← hx']
    exact h

@[simp] theorem append_toList (ξ η : Chro Loc Val) (h : ξ.c ⊆ η.o) :
    (ξ.append η h).toList = ξ.toList ++ η.toList := rfl

@[simp] theorem append_o (ξ η : Chro Loc Val) (h : ξ.c ⊆ η.o) :
    (ξ.append η h).o = ξ.o := rfl

@[simp] theorem append_c (ξ η : Chro Loc Val) (h : ξ.c ⊆ η.o) :
    (ξ.append η h).c = η.c := by
  change listC (ξ.first :: (ξ.rest ++ η.first :: η.rest)) = listC η.toList
  cases hr : ξ.rest with
  | nil => rfl
  | cons U l =>
      change listC (ξ.first :: U :: (l ++ η.first :: η.rest)) = _
      rw [listC_cons_cons]
      change listC ((U :: l) ++ η.first :: η.rest) = _
      rw [listC_append]
      rfl

@[simp] theorem append_own (ξ η : Chro Loc Val) (h : ξ.c ⊆ η.o) :
    (ξ.append η h).own = ξ.own ∪ η.own := by
  simp only [own, append_toList, listOwn_append]

theorem append_assoc (ξ η ζ : Chro Loc Val) (h₁ : ξ.c ⊆ η.o) (h₂ : η.c ⊆ ζ.o) :
    (ξ.append η h₁).append ζ (by simpa using h₂)
      = ξ.append (η.append ζ h₂) (by simpa using h₁) := by
  apply ext_toList
  simp [List.append_assoc]

end Chro

/-- An `X`-pre-trace `α ξ ω ◁ r`. -/
structure PreTrace (Loc Val : Type) (A : Type u) where
  /-- The initial view `α`. -/
  ivw : View Loc
  /-- The chronicle `ξ`. -/
  ch : Chro Loc Val
  /-- The final view `ω`. -/
  fvw : View Loc
  /-- The returned value `r`. -/
  ret : A

/-- The paper's trace conditions. -/
structure IsTrace {A : Type u} (τ : PreTrace Loc Val A) : Prop where
  /-- Every transition consists of well-formed memories. -/
  wf : ∀ T ∈ τ.ch.toList, T.WF
  /-- `ξ.o ↞ α`. -/
  openPts : PointsDownInto τ.ivw τ.ch.o
  /-- `α ⊑ ω`. -/
  mono : τ.ivw ≤ τ.fvw
  /-- `ω ↠ ξ.c`. -/
  closePts : PointsDownInto τ.fvw τ.ch.c
  /-- Local messages are bounded by the delimiting views. -/
  own : ∀ ν ∈ τ.ch.own, τ.ivw ≤ ν.vw ∧ ν.vw ≤ τ.fvw ∧ τ.ivw ν.lc < ν.t

/-- Concatenation of traces at a compatible seam is a trace: the paper leaves
the clause `∈ Trace Y` in the definition of `>>=` as a side condition, and this
lemma shows it is automatic. -/
theorem IsTrace.append {A B : Type u} {τ : PreTrace Loc Val A} {υ : PreTrace Loc Val B}
    (hτ : IsTrace τ) (hυ : IsTrace υ) (hseam : τ.fvw ≤ υ.ivw) (h : τ.ch.c ⊆ υ.ch.o) :
    IsTrace (⟨τ.ivw, τ.ch.append υ.ch h, υ.fvw, υ.ret⟩ : PreTrace Loc Val B) where
  wf := by
    intro T hT
    rw [Chro.append_toList, List.mem_append] at hT
    exact hT.elim (hτ.wf T) (hυ.wf T)
  openPts := by simpa using hτ.openPts
  mono := le_trans hτ.mono (le_trans hseam hυ.mono)
  closePts := by simpa using hυ.closePts
  own := by
    intro ν hν
    rw [Chro.append_own] at hν
    rcases hν with hν | hν
    · obtain ⟨h1, h2, h3⟩ := hτ.own ν hν
      exact ⟨h1, le_trans h2 (le_trans hseam hυ.mono), h3⟩
    · obtain ⟨h1, h2, h3⟩ := hυ.own ν hν
      refine ⟨le_trans hτ.mono (le_trans hseam h1), h2, ?_⟩
      exact lt_of_le_of_lt ((le_trans hτ.mono hseam) ν.lc) h3

end Isotope.Elgot.RA
