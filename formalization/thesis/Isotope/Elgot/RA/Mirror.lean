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


/-! ## Deriving the right operand's decomposition

The three lemmas above take both decompositions as data.  In the intended use
only the left one is given: the right operand `υ` of the seam is an arbitrary
trace whose opening memory happens to contain the message the `𝔞`-rewrite acts
on.  The lemmas of this section recover the decomposition `υ = n ⊎ {ε}` from
that, which is possible because *memories only grow along a chronicle* (journal
§7.2, p.28), so a message of the opening memory belongs to every memory. -/

/-- `T ⊖ {ε}`: remove `ε` from both memories of a transition — the inverse of
`Transition.insertMsg` on transitions containing `ε`. -/
def Transition.deleteMsg (ε : Msg Loc Val) (T : Transition Loc Val) :
    Transition Loc Val :=
  ⟨T.opening \ {ε}, T.closing \ {ε}⟩

@[simp] theorem Transition.deleteMsg_opening (ε : Msg Loc Val) (T : Transition Loc Val) :
    (T.deleteMsg ε).opening = T.opening \ {ε} := rfl

@[simp] theorem Transition.deleteMsg_closing (ε : Msg Loc Val) (T : Transition Loc Val) :
    (T.deleteMsg ε).closing = T.closing \ {ε} := rfl

theorem Transition.insertMsg_deleteMsg {ε : Msg Loc Val} {T : Transition Loc Val}
    (ho : ε ∈ T.opening) (hc : ε ∈ T.closing) : (T.deleteMsg ε).insertMsg ε = T := by
  cases T with
  | mk o c =>
      simp only [Transition.insertMsg, Transition.deleteMsg, Transition.mk.injEq]
      exact ⟨Set.insert_diff_self ho, Set.insert_diff_self hc⟩

/-- In a chronicle whose transitions all grow (`μ ⊆ ρ`), the opening memory is
contained in every one of the memories. -/
theorem listO_sub_of_mono : ∀ (l : List (Transition Loc Val)), List.IsChain Adj l →
    (∀ T ∈ l, T.opening ⊆ T.closing) → ∀ T ∈ l, listO l ⊆ T.opening
  | [], _, _, _, hT => absurd hT (by simp)
  | S :: r, hc, hst, T, hT => by
      rcases List.mem_cons.mp hT with rfl | hT
      · rw [listO_cons]
      · have hne : r ≠ [] := by rintro rfl; simp at hT
        have ih := listO_sub_of_mono r (List.isChain_cons.mp hc).2
          (fun U hU ↦ hst U (by simp [hU])) T hT
        rw [listO_cons]
        exact subset_trans (subset_trans (hst S (by simp)) (adj_listO hc hne)) ih

/-- **The decomposition `ξ = n ⊎ {ε}`.**  Deleting `ε` from every memory and
adding it back is the identity, provided `ε` lies in the opening memory. -/
theorem map_insertMsg_deleteMsg {c : Chro Loc Val}
    (hmono : ∀ T ∈ c.toList, T.opening ⊆ T.closing) {ε : Msg Loc Val} (hε : ε ∈ c.o) :
    (c.toList.map (Transition.deleteMsg ε)).map (Transition.insertMsg ε) = c.toList := by
  have key : c.toList.map (Transition.insertMsg ε ∘ Transition.deleteMsg ε)
      = c.toList.map id := by
    refine List.map_congr_left (fun T hT ↦ ?_)
    have ho : ε ∈ T.opening := listO_sub_of_mono c.toList c.chain_toList hmono T hT hε
    exact Transition.insertMsg_deleteMsg ho (hmono T hT ho)
  rw [List.map_map, key, List.map_id]

/-- The deleted message is absent from the decomposition: the disjointness the
paper writes as `⊎`. -/
theorem listFree_map_deleteMsg (ε : Msg Loc Val) (l : List (Transition Loc Val)) :
    listFree ε (l.map (Transition.deleteMsg ε)) := by
  rintro _ hT
  obtain ⟨S, _, rfl⟩ := List.mem_map.mp hT
  exact ⟨fun h ↦ h.2 rfl, fun h ↦ h.2 rfl⟩

/-- Any other message absent from the chronicle is absent from the
decomposition. -/
theorem listFree_map_deleteMsg_of {ν ε : Msg Loc Val} {l : List (Transition Loc Val)}
    (h : ∀ T ∈ l, ν ∉ T.opening ∧ ν ∉ T.closing) :
    listFree ν (l.map (Transition.deleteMsg ε)) := by
  rintro _ hT
  obtain ⟨S, hS, rfl⟩ := List.mem_map.mp hT
  exact ⟨fun hc ↦ (h S hS).1 hc.1, fun hc ↦ (h S hS).2 hc.1⟩

theorem isChain_map_deleteMsg {ε : Msg Loc Val} {l : List (Transition Loc Val)}
    (h : List.IsChain Adj l) : List.IsChain Adj (l.map (Transition.deleteMsg ε)) :=
  List.isChain_map_of_isChain _ (fun _ _ hab _ hx ↦ ⟨hab hx.1, hx.2⟩) h

theorem isChain_map_insertMsg {ε : Msg Loc Val} {l : List (Transition Loc Val)}
    (h : List.IsChain Adj l) : List.IsChain Adj (l.map (Transition.insertMsg ε)) :=
  List.isChain_map_of_isChain _ (fun _ _ hab ↦ Transition.insertMsg_adj hab) h

/-! ## Where the rewritten messages sit in the closing memory -/

/-- The closing memory of `T :: (m ++ [U]) ⊎ {·}` is that of the last
transition. -/
theorem listC_cons_map_concat (f : Transition Loc Val → Transition Loc Val)
    (T U : Transition Loc Val) (m : List (Transition Loc Val)) :
    listC (T :: (m ++ [U]).map f) = (f U).closing := by
  rw [List.map_append, List.map_cons, List.map_nil, ← List.cons_append, listC_append]
  rfl

/-- The closing memory of an `𝔞`-rule's source and target differ exactly by the
rewritten messages: both are obtained from one memory `X` by adding them. -/
theorem exists_closing_of_aShape {f g : Transition Loc Val → Transition Loc Val}
    {c₁ c₂ : Chro Loc Val} {l m : List (Transition Loc Val)} {T S : Transition Loc Val}
    (h₁ : c₁.toList = l ++ T :: m.map f) (h₂ : c₂.toList = l ++ S :: m.map g) :
    (m = [] ∧ c₁.c = T.closing ∧ c₂.c = S.closing) ∨
      ∃ U ∈ m, c₁.c = (f U).closing ∧ c₂.c = (g U).closing := by
  rcases List.eq_nil_or_concat' m with rfl | ⟨m', U, rfl⟩
  · exact Or.inl ⟨rfl, by rw [Chro.c, h₁, listC_append]; rfl,
      by rw [Chro.c, h₂, listC_append]; rfl⟩
  · exact Or.inr ⟨U, by simp, by rw [Chro.c, h₁, listC_append, listC_cons_map_concat],
      by rw [Chro.c, h₂, listC_append, listC_cons_map_concat]⟩

theorem listO_map_insertMsg (ν : Msg Loc Val) {l : List (Transition Loc Val)}
    (h : l ≠ []) : listO (l.map (Transition.insertMsg ν)) = insert ν (listO l) := by
  cases l with
  | nil => exact absurd rfl h
  | cons T l => rfl

/-- Cancelling a common inserted element on the left of an inclusion. -/
theorem subset_of_insert_subset_insert {a : Msg Loc Val} {X Y : Memory Loc Val}
    (h : insert a X ⊆ insert a Y) (ha : a ∉ X) : X ⊆ Y := by
  intro x hx
  rcases h (Set.mem_insert_of_mem _ hx) with rfl | hxy
  · exact absurd hx ha
  · exact hxy

/-! ## The seam form: `Ls ↔ Ti` with the right operand's decomposition derived -/

/-- **`Ls ↔ Ti` at the seam.**  Let the left operand of a seam be
`Ti`-rewritten from `c₁` to `c₂`, and let `υ` be any right operand whose
memories grow and in which the tightened message `ν` does not already occur.
Then `υ` `Ls`-rewrites to some `d`, the seam of `c₁` with `d` is defined, and a
single `Ti`-rewrite carries it to the seam of `c₂` with `υ`.

This is Deferral of Closure's mirroring with the decomposition of the right
operand *derived* rather than assumed: `ε` lies in `c₂`'s closing memory, hence
in `υ`'s opening memory, hence — memories only grow — in every memory of `υ`.

**Original work**; see the file header. -/
theorem seam_tighten {Ra Rg : RuleSet} (hTi : Rule.Ti ∈ Ra) (hLs : Rule.Ls ∈ Rg)
    {α : View Loc} {c₁ c₂ : Chro Loc Val}
    {l m : List (Transition Loc Val)} {μ ρ : Memory Loc Val} {ν ε : Msg Loc Val}
    (hle : Msg.LeVw ν ε) (hνμ : ν ∉ μ) (hνρ : ν ∉ ρ) (hεμ : ε ∉ μ) (hερ : ε ∉ ρ)
    (hfνm : listFree ν m) (hfεm : listFree ε m)
    (h₁ : c₁.toList = l ++ ⟨μ, insert ν ρ⟩ :: m.map (Transition.insertMsg ν))
    (h₂ : c₂.toList = l ++ ⟨μ, insert ε ρ⟩ :: m.map (Transition.insertMsg ε))
    {υ : PreTrace Loc Val B}
    (hmono : ∀ T ∈ υ.ch.toList, T.opening ⊆ T.closing)
    (hνυ : ∀ T ∈ υ.ch.toList, ν ∉ T.opening ∧ ν ∉ T.closing)
    (k₂ : c₂.c ⊆ υ.ch.o) :
    ∃ (d : Chro Loc Val) (k₁ : c₁.c ⊆ d.o),
      Step Rg υ ⟨υ.ivw, d, υ.fvw, υ.ret⟩ ∧
      Step Ra (⟨α, c₁.append d k₁, υ.fvw, υ.ret⟩ : PreTrace Loc Val B)
        ⟨α, c₂.append υ.ch k₂, υ.fvw, υ.ret⟩ := by
  classical
  -- the two closing memories differ exactly by `ν` versus `ε`
  obtain ⟨X, hX₁, hX₂, hXε⟩ :
      ∃ X : Memory Loc Val, c₁.c = insert ν X ∧ c₂.c = insert ε X ∧ ε ∉ X := by
    rcases exists_closing_of_aShape h₁ h₂ with ⟨-, e₁, e₂⟩ | ⟨U, hU, e₁, e₂⟩
    · exact ⟨ρ, e₁, e₂, hερ⟩
    · exact ⟨U.closing, e₁, e₂, (hfεm U hU).2⟩
  have hευ : ε ∈ υ.ch.o := k₂ (hX₂ ▸ Set.mem_insert _ _)
  -- decompose `υ` as `n ⊎ {ε}`
  have hnne : υ.ch.toList.map (Transition.deleteMsg ε) ≠ [] := by
    simp [υ.ch.toList_ne_nil]
  have hnchain : List.IsChain Adj (υ.ch.toList.map (Transition.deleteMsg ε)) :=
    isChain_map_deleteMsg υ.ch.chain_toList
  have hυn : υ.ch.toList =
      (υ.ch.toList.map (Transition.deleteMsg ε)).map (Transition.insertMsg ε) :=
    (map_insertMsg_deleteMsg hmono hευ).symm
  have hfεn : listFree ε (υ.ch.toList.map (Transition.deleteMsg ε)) :=
    listFree_map_deleteMsg ε _
  have hfνn : listFree ν (υ.ch.toList.map (Transition.deleteMsg ε)) :=
    listFree_map_deleteMsg_of hνυ
  set d : Chro Loc Val :=
    Chro.ofList ((υ.ch.toList.map (Transition.deleteMsg ε)).map (Transition.insertMsg ν))
      (by simpa using υ.ch.toList_ne_nil) (isChain_map_insertMsg hnchain) with hd
  have hdl : d.toList =
      (υ.ch.toList.map (Transition.deleteMsg ε)).map (Transition.insertMsg ν) :=
    Chro.ofList_toList _ _ _
  have hdo : d.o = insert ν (listO (υ.ch.toList.map (Transition.deleteMsg ε))) := by
    rw [Chro.o, hdl, listO_map_insertMsg ν hnne]
  have hεn : ε ∉ listO (υ.ch.toList.map (Transition.deleteMsg ε)) := by
    cases hnl : υ.ch.toList.map (Transition.deleteMsg ε) with
    | nil => exact absurd hnl hnne
    | cons T n' => exact (hfεn T (by simp [hnl])).1
  have hoυ : υ.ch.o = insert ε (listO (υ.ch.toList.map (Transition.deleteMsg ε))) := by
    conv_lhs => rw [Chro.o, hυn]
    rw [listO_map_insertMsg ε hnne]
  have k₁ : c₁.c ⊆ d.o := by
    rw [hdo, hX₁]
    exact Set.insert_subset_insert
      (subset_of_insert_subset_insert (by rw [← hX₂, ← hoυ]; exact k₂) hXε)
  obtain ⟨hls, hti⟩ :=
    mirror_tighten hle hνμ hνρ hεμ hερ hfνm hfεm hfνn hfεn h₁ h₂ hυn hdl k₁ k₂
  exact ⟨d, k₁, Step.chro hLs hls, Step.chro hTi hti⟩

/-! ## The seam form: `Ex ↔ Ab`

This is the case the paper spells out (journal p.41): "instead of `Ab`-rewriting
some trace `τ ∈ P₁` and then 'binding' it with a trace `π ∈ f(τ.vl)`, we can
instead mirror its effect by `Ex`-rewriting `π` to make its messages match
`τ`'s, bind those together, and then `Ab`-rewrite after the bind." -/

theorem listO_map_insertMsg₂ (ν ε : Msg Loc Val) {l : List (Transition Loc Val)}
    (h : l ≠ []) :
    listO (l.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
      = insert ν (insert ε (listO l)) := by
  cases l with
  | nil => exact absurd rfl h
  | cons T l => rfl

theorem isChain_map_insertMsg₂ {ν ε : Msg Loc Val} {l : List (Transition Loc Val)}
    (h : List.IsChain Adj l) :
    List.IsChain Adj (l.map (fun T ↦ (T.insertMsg ε).insertMsg ν)) :=
  List.isChain_map_of_isChain _
    (fun _ _ hab ↦ Transition.insertMsg_adj (Transition.insertMsg_adj hab)) h

/-- **`Ex ↔ Ab` at the seam.**  The left operand of a seam is `Ab`-rewritten,
merging the dovetailing local pair `ν ⤙ ε` into `ε[i↦ν.i]`; the right operand
`υ` carries `ε[i↦ν.i]` as an environment message and neither `ν` nor `ε`.  Then
`υ` `Ex`-rewrites *backwards*, splitting `ε[i↦ν.i]` into `ν` and `ε`, and a
single `Ab`-rewrite carries the seam of `c₁` with the split `υ` to the seam of
`c₂` with `υ`.

**Original work**; see the file header. -/
theorem seam_absorb {Ra Rg : RuleSet} (hAb : Rule.Ab ∈ Ra) (hEx : Rule.Ex ∈ Rg)
    {α : View Loc} {c₁ c₂ : Chro Loc Val}
    {l m : List (Transition Loc Val)} {μ ρ : Memory Loc Val} {ν ε : Msg Loc Val}
    (hdt : Msg.Dovetail ν ε)
    (hνμ : ν ∉ μ) (hνρ : ν ∉ ρ) (hεμ : ε ∉ μ) (hερ : ε ∉ ρ)
    (hsμ : ε.setI ν.i hdt.i_lt_t ∉ μ) (hsρ : ε.setI ν.i hdt.i_lt_t ∉ ρ)
    (hfνm : listFree ν m) (hfεm : listFree ε m)
    (hfsm : listFree (ε.setI ν.i hdt.i_lt_t) m)
    (h₁ : c₁.toList =
      l ++ ⟨μ, insert ν (insert ε ρ)⟩ ::
        m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (h₂ : c₂.toList =
      l ++ ⟨μ, insert (ε.setI ν.i hdt.i_lt_t) ρ⟩ ::
        m.map (Transition.insertMsg (ε.setI ν.i hdt.i_lt_t)))
    {υ : PreTrace Loc Val B}
    (hmono : ∀ T ∈ υ.ch.toList, T.opening ⊆ T.closing)
    (hνυ : ∀ T ∈ υ.ch.toList, ν ∉ T.opening ∧ ν ∉ T.closing)
    (hευ : ∀ T ∈ υ.ch.toList, ε ∉ T.opening ∧ ε ∉ T.closing)
    (k₂ : c₂.c ⊆ υ.ch.o) :
    ∃ (d : Chro Loc Val) (k₁ : c₁.c ⊆ d.o),
      Step Rg υ ⟨υ.ivw, d, υ.fvw, υ.ret⟩ ∧
      Step Ra (⟨α, c₁.append d k₁, υ.fvw, υ.ret⟩ : PreTrace Loc Val B)
        ⟨α, c₂.append υ.ch k₂, υ.fvw, υ.ret⟩ := by
  classical
  set ε' : Msg Loc Val := ε.setI ν.i hdt.i_lt_t with hε'
  obtain ⟨X, hX₁, hX₂, hXs⟩ :
      ∃ X : Memory Loc Val,
        c₁.c = insert ν (insert ε X) ∧ c₂.c = insert ε' X ∧ ε' ∉ X := by
    rcases exists_closing_of_aShape h₁ h₂ with ⟨-, e₁, e₂⟩ | ⟨U, hU, e₁, e₂⟩
    · exact ⟨ρ, e₁, e₂, hsρ⟩
    · exact ⟨U.closing, e₁, e₂, (hfsm U hU).2⟩
  have hsυ : ε' ∈ υ.ch.o := k₂ (hX₂ ▸ Set.mem_insert _ _)
  have hnne : υ.ch.toList.map (Transition.deleteMsg ε') ≠ [] := by
    simp [υ.ch.toList_ne_nil]
  have hnchain : List.IsChain Adj (υ.ch.toList.map (Transition.deleteMsg ε')) :=
    isChain_map_deleteMsg υ.ch.chain_toList
  have hυn : υ.ch.toList =
      (υ.ch.toList.map (Transition.deleteMsg ε')).map (Transition.insertMsg ε') :=
    (map_insertMsg_deleteMsg hmono hsυ).symm
  have hfsn : listFree ε' (υ.ch.toList.map (Transition.deleteMsg ε')) :=
    listFree_map_deleteMsg ε' _
  have hfνn : listFree ν (υ.ch.toList.map (Transition.deleteMsg ε')) :=
    listFree_map_deleteMsg_of hνυ
  have hfεn : listFree ε (υ.ch.toList.map (Transition.deleteMsg ε')) :=
    listFree_map_deleteMsg_of hευ
  set d : Chro Loc Val :=
    Chro.ofList ((υ.ch.toList.map (Transition.deleteMsg ε')).map
        (fun T ↦ (T.insertMsg ε).insertMsg ν))
      (by simpa using υ.ch.toList_ne_nil) (isChain_map_insertMsg₂ hnchain) with hd
  have hdl : d.toList =
      (υ.ch.toList.map (Transition.deleteMsg ε')).map
        (fun T ↦ (T.insertMsg ε).insertMsg ν) := Chro.ofList_toList _ _ _
  have hdo : d.o =
      insert ν (insert ε (listO (υ.ch.toList.map (Transition.deleteMsg ε')))) := by
    rw [Chro.o, hdl, listO_map_insertMsg₂ ν ε hnne]
  have hoυ : υ.ch.o = insert ε' (listO (υ.ch.toList.map (Transition.deleteMsg ε'))) := by
    conv_lhs => rw [Chro.o, hυn]
    rw [listO_map_insertMsg ε' hnne]
  have k₁ : c₁.c ⊆ d.o := by
    rw [hdo, hX₁]
    exact Set.insert_subset_insert (Set.insert_subset_insert
      (subset_of_insert_subset_insert (by rw [← hX₂, ← hoυ]; exact k₂) hXs))
  obtain ⟨hex, hab⟩ :=
    mirror_absorb hdt hνμ hνρ hεμ hερ hsμ hsρ hfνm hfεm hfsm hfνn hfεn hfsn h₁ h₂
      hυn hdl k₁ k₂
  exact ⟨d, k₁, Step.chro hEx hex, Step.chro hAb hab⟩

end Isotope.Elgot.RA
