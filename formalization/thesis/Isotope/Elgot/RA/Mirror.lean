import Isotope.Elgot.RA.Castling

/-!
# Deferral of Closure: the `𝔞`/`𝔤` mirroring at the bind seam

Dvir, Kammar and Lahav's **Lemma 8.5 (Deferral of Closure)** (journal §8.2,
p.41; ESOP full version Lemma 7.5) reads, verbatim:

> Let `𝔠 ⊆ ★ ⊆ 𝔠𝔞`.  For all `Pᵢ ∈ G Xᵢ` and `f : X₁ → G X₂`:
> `(P★₁ >>=_G f★)★ = (P₁ >>=_G f)★`  and  `(P★₁ ∥_G P★₂)★ = (P₁ ∥_G P₂)★`.

Its proof (journal Appendix A, pp.48–49) turns on one informal observation,
which the paper states in prose only (journal p.41, verbatim):

> "In the proof we rely on the fact that `𝔤` has a counterpart for every
> closure rule in `𝔞`: `Ls ↔ Ti`; `Ex ↔ Ab`; `Cn ↔ Di`.  Figures 12 to 15
> depict this correspondence when comparing the left and right sides of the
> figure: **the messages that need to be local to apply an `𝔞`-closure need to
> be environment messages in their `𝔤`-counterpart, and the rewrite goes in the
> opposite direction.**  For example, instead of `Ab`-rewriting some trace
> `τ ∈ P₁` and then 'binding' it with a trace `π ∈ f(τ.vl)`, we can instead
> mirror its effect by `Ex`-rewriting `π` to make its messages match `τ`'s,
> bind those together, and then `Ab`-rewrite after the bind."

**This file makes that observation a theorem**, in the three instances the
paper names.  Each of `mirror_tighten`, `mirror_absorb`, `mirror_dilute` says:

> if the left operand of a seam is rewritten by the `𝔞` rule `x` acting on the
> messages `ν`, `ε`, and the right operand carries those same messages as
> *environment* messages, then the right operand can be rewritten by the mirror
> `𝔤` rule `y` **in the opposite direction**, and the two seams are related by a
> single `x`-rewrite spanning the whole concatenation.

The paper proves nothing of the sort — it gives the sentence quoted above and
an appeal to Figures 12–15 — so **everything here is original work**, not a
port.  What *is* transcribed is the correspondence itself (`Ls ↔ Ti`,
`Ex ↔ Ab`, `Cn ↔ Di`, journal p.41) and the rules being mirrored
(`Isotope/Elgot/RA/Rewrite.lean`).

## Why the mirroring is forced by the shape of the rules

Read off the two displays of each pair, with `η` the rewritten chronicle
suffix:

| `𝔤` rule (`ε` an environment message) | `𝔞` rule (`ν`, `ε` local) |
|---|---|
| `Ls`: `η ⊎ {ε} → η ⊎ {ν}` | `Ti`: `⟨μ,ρ⊎{ν}⟩ η⊎{ν} → ⟨μ,ρ⊎{ε}⟩ η⊎{ε}` |
| `Ex`: `η ⊎ {ε[i↦ν.i]} → η ⊎ {ν,ε}` | `Ab`: `⟨μ,ρ⊎{ν,ε}⟩ η⊎{ν,ε} → ⟨μ,ρ⊎{ε[i↦ν.i]}⟩ η⊎{ε[i↦ν.i]}` |
| `Cn`: `η ⊎ {ν,ε} → (η ⊎ {ν})[↑ε]` | `Di`: `(⟨μ,ρ⊎{ν}⟩ η⊎{ν})[↑ε] → ⟨μ,ρ⊎{ν,ε}⟩ η⊎{ν,ε}` |

On the *suffix alone* the two columns are the same relation read backwards.
So if the `𝔞`-rewrite of the left operand has suffix `m` and the right operand
is `n ⊎ {ε}` (resp. `n ⊎ {ε[i↦ν.i]}`, `n ⊎ {ν,ε}`), then applying the `𝔤` rule
to the right operand turns it into `n ⊎ {ν}` (resp. `n ⊎ {ν,ε}`,
`(n ⊎ {ν})[↑ε]`), and the concatenated chronicles are related by the *same*
`𝔞` rule with suffix `m ++ n`.  That is exactly what the three lemmas below
say, and it is why the paper can defer the closure.

## What is *not* here

* The mirroring is stated with the two decompositions supplied by the caller.
  For `Ti` and `Ab` we additionally derive the right operand's decomposition
  from the trace conditions (`seam_tighten`, `seam_absorb`); for `Di` we do
  not, because the seam's view conditions after a pull need Lemma 7.6 with
  side conditions that the caller must establish anyway.
* Deferral of Closure itself is *not* proved.  Getting from these lemmas to
  `(P★ >>=_G f★)★ = (P >>=_G f)★` needs, in addition, the freshness side
  conditions discharged uniformly, an induction over rewrite *sequences* in
  both operands, and the symmetric statements for the right operand.  See the
  honest boundary in `Isotope/Elgot/RA/Abstract.lean`.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {A B : Type u}

/-! ## `Ls ↔ Ti` -/

/-- **The `Ls ↔ Ti` mirroring** (journal p.41).  The left operand of a seam is
`Ti`-rewritten, replacing the local message `ν` by `ε` from the transition
`⟨μ, ρ ⊎ {ν}⟩` onwards; the right operand carries `ε` as an environment
message.  Then the right operand `Ls`-rewrites *backwards*, `ε ↦ ν`, and the
two seams are related by a single `Ti`-rewrite whose suffix is the
concatenation of the two suffixes.

**Original work**: the paper asserts the correspondence in prose and proves
nothing about it. -/
theorem mirror_tighten
    {l m n : List (Transition Loc Val)} {μ ρ : Memory Loc Val} {ν ε : Msg Loc Val}
    (hle : Msg.LeVw ν ε)
    (hνμ : ν ∉ μ) (hνρ : ν ∉ ρ) (hεμ : ε ∉ μ) (hερ : ε ∉ ρ)
    (hfνm : listFree ν m) (hfεm : listFree ε m)
    (hfνn : listFree ν n) (hfεn : listFree ε n)
    {c₁ c₂ d₁ d₂ : Chro Loc Val}
    (h₁ : c₁.toList = l ++ ⟨μ, insert ν ρ⟩ :: m.map (Transition.insertMsg ν))
    (h₂ : c₂.toList = l ++ ⟨μ, insert ε ρ⟩ :: m.map (Transition.insertMsg ε))
    (e₁ : d₁.toList = n.map (Transition.insertMsg ε))
    (e₂ : d₂.toList = n.map (Transition.insertMsg ν))
    (k₁ : c₁.c ⊆ d₂.o) (k₂ : c₂.c ⊆ d₁.o) :
    ChroStep Rule.Ls d₁ d₂ ∧
      ChroStep Rule.Ti (c₁.append d₂ k₁) (c₂.append d₁ k₂) := by
  refine ⟨ChroStep.loosen d₁ d₂ [] n ν ε hle hfεn hfνn (by simpa using e₁)
      (by simpa using e₂),
    ChroStep.tighten _ _ l (m ++ n) μ ρ ν ε hle hνμ hνρ hεμ hερ
      (fun T hT ↦ (List.mem_append.mp hT).elim (hfνm T) (hfνn T))
      (fun T hT ↦ (List.mem_append.mp hT).elim (hfεm T) (hfεn T)) ?_ ?_⟩
  · rw [Chro.append_toList, h₁, e₂, List.map_append]
    simp [List.append_assoc]
  · rw [Chro.append_toList, h₂, e₁, List.map_append]
    simp [List.append_assoc]

/-! ## `Ex ↔ Ab` -/

/-- **The `Ex ↔ Ab` mirroring** (journal p.41): the case the paper itself uses
as its example — "instead of `Ab`-rewriting some trace `τ ∈ P₁` and then
'binding' it with a trace `π ∈ f(τ.vl)`, we can instead mirror its effect by
`Ex`-rewriting `π` to make its messages match `τ`'s, bind those together, and
then `Ab`-rewrite after the bind."

**Original work.** -/
theorem mirror_absorb
    {l m n : List (Transition Loc Val)} {μ ρ : Memory Loc Val} {ν ε : Msg Loc Val}
    (hdt : Msg.Dovetail ν ε)
    (hνμ : ν ∉ μ) (hνρ : ν ∉ ρ) (hεμ : ε ∉ μ) (hερ : ε ∉ ρ)
    (hsμ : ε.setI ν.i hdt.i_lt_t ∉ μ) (hsρ : ε.setI ν.i hdt.i_lt_t ∉ ρ)
    (hfνm : listFree ν m) (hfεm : listFree ε m)
    (hfsm : listFree (ε.setI ν.i hdt.i_lt_t) m)
    (hfνn : listFree ν n) (hfεn : listFree ε n)
    (hfsn : listFree (ε.setI ν.i hdt.i_lt_t) n)
    {c₁ c₂ d₁ d₂ : Chro Loc Val}
    (h₁ : c₁.toList =
      l ++ ⟨μ, insert ν (insert ε ρ)⟩ ::
        m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (h₂ : c₂.toList =
      l ++ ⟨μ, insert (ε.setI ν.i hdt.i_lt_t) ρ⟩ ::
        m.map (Transition.insertMsg (ε.setI ν.i hdt.i_lt_t)))
    (e₁ : d₁.toList = n.map (Transition.insertMsg (ε.setI ν.i hdt.i_lt_t)))
    (e₂ : d₂.toList = n.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (k₁ : c₁.c ⊆ d₂.o) (k₂ : c₂.c ⊆ d₁.o) :
    ChroStep Rule.Ex d₁ d₂ ∧
      ChroStep Rule.Ab (c₁.append d₂ k₁) (c₂.append d₁ k₂) := by
  refine ⟨ChroStep.expel d₁ d₂ [] n ν ε hdt hfsn hfνn hfεn (by simpa using e₁)
      (by simpa using e₂),
    ChroStep.absorb _ _ l (m ++ n) μ ρ ν ε hdt hνμ hνρ hεμ hερ hsμ hsρ
      (fun T hT ↦ (List.mem_append.mp hT).elim (hfνm T) (hfνn T))
      (fun T hT ↦ (List.mem_append.mp hT).elim (hfεm T) (hfεn T))
      (fun T hT ↦ (List.mem_append.mp hT).elim (hfsm T) (hfsn T)) ?_ ?_⟩
  · rw [Chro.append_toList, h₁, e₂, List.map_append]
    simp [List.append_assoc]
  · rw [Chro.append_toList, h₂, e₁, List.map_append]
    simp [List.append_assoc]

/-! ## `Cn ↔ Di` -/

/-- **The `Cn ↔ Di` mirroring** (journal p.41), the pair the paper calls its
"most complicated" case.  Unlike the other two, both rules pull the *whole*
pre-trace along `ε`, so the statement is at the level of `Step` rather than
`ChroStep`, and the delimiting views of the two seams differ by a pull.

**Original work.** -/
theorem mirror_dilute {Rg Ra : RuleSet} (hCn : Rule.Cn ∈ Rg) (hDi : Rule.Di ∈ Ra)
    {l m n : List (Transition Loc Val)} {μ ρ : Memory Loc Val} {ν ε : Msg Loc Val}
    (hde : Msg.DovetailEq ν ε)
    (hεμ : ε ∉ μ) (hερ : ε ∉ ρ) (hνρ : ν ∉ ρ)
    (hfνm : listFree ν m) (hfεm : listFree ε m)
    (hfνn : listFree ν n) (hfεn : listFree ε n)
    {c₁ c₂ d₁ d₂ : Chro Loc Val} {α : View Loc} {α' ω' : View Loc} {s : B}
    (h₁ : c₁.toList =
      (l ++ ⟨μ, insert ν ρ⟩ :: m.map (Transition.insertMsg ν)).map (Transition.pull ε))
    (h₂ : c₂.toList =
      l ++ ⟨μ, insert ν (insert ε ρ)⟩ ::
        m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (e₁ : d₁.toList = n.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (e₂ : d₂.toList = (n.map (Transition.insertMsg ν)).map (Transition.pull ε))
    (k₁ : c₁.c ⊆ d₂.o) (k₂ : c₂.c ⊆ d₁.o) :
    Step Rg (⟨α', d₁, ω', s⟩ : PreTrace Loc Val B)
        ⟨View.pull ε α', d₂, View.pull ε ω', s⟩ ∧
      Step Ra
        (⟨View.pull ε α, c₁.append d₂ k₁, View.pull ε ω', s⟩ : PreTrace Loc Val B)
        ⟨α, c₂.append d₁ k₂, ω', s⟩ := by
  refine ⟨Step.condense hCn [] n ν ε hde hfνn hfεn (by simpa using e₁)
      (by simpa using e₂),
    Step.dilute hDi l (m ++ n) μ ρ ν ε hde hεμ hερ hνρ
      (fun T hT ↦ (List.mem_append.mp hT).elim (hfνm T) (hfνn T))
      (fun T hT ↦ (List.mem_append.mp hT).elim (hfεm T) (hfεn T)) ?_ ?_⟩
  · rw [Chro.append_toList, h₁, e₂, List.map_append, ← List.map_append]
    simp [List.append_assoc]
  · rw [Chro.append_toList, h₂, e₁, List.map_append]
    simp [List.append_assoc]

end Isotope.Elgot.RA
