import Isotope.Elgot.RA.GData
import Isotope.Elgot.RA.Monad

/-!
# Proposition 7.5: the operations absorb the generating rules

Dvir, Kammar and Lahav, journal §7.3, p.30:

> We identify a set of closure rules `𝔤 ≜ {Ls, Ex, Cn}` under which the
> operations of the null model are closed: `return_N` is pointwise closed under
> `𝔤`; if `f` is pointwise `𝔤`-closed, then `>>=_N f` is `𝔤`-closed; and
> similarly for the effect operations.
>
> **Proposition 7.5.** For all `Pᵢ ∈ G Xᵢ` and `f : X₁ → G X₂`:
> `P₁ >>=_N f = P₁ >>=_G f` … and `return_N = return_G`.

The paper's argument is a sketch: one sentence each for `Ls` and `Ex`, and for
`Cn` a paragraph (pp.33–34) it calls "harder to demonstrate", whose content is

> to show that bind preserves the rule, we replace an application of condense
> after binding the traces with applications of condense (with the same
> messages) on each of the traces before binding.  This replacement is subtle
> because the delimiting views change, and thus the condition `κ ⊑ σ` imposed on
> binding the traces changes to `κ[↑ε] ⊑ σ[↑ε]`.  The condition still holds due
> to Lemma 7.6 …

That is exactly the proof of `bindGen_closed` below: a `𝔤`-rewrite of a
concatenation splits, positionally, into a `𝔤`-rewrite of each factor, and the
seam condition survives by Lemma 7.6.  The split is positional because all three
`𝔤` rules preserve the number of transitions.  Since the paper gives no proof,
**the proofs here are ours**.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {A B : Type u}

/-! ## `return` -/

/-- Every rule of `𝔤` maintains `α = ω`: `Ls` and `Ex` leave both delimiting
views alone, and `Cn` pulls both along the same message. -/
theorem Step.ivw_eq_fvw {R : RuleSet} (hR : R ⊆ gRules) {τ π : PreTrace Loc Val A}
    (h : Step R τ π) (hτ : τ.ivw = τ.fvw) : π.ivw = π.fvw := by
  cases h with
  | chro _ _ => exact hτ
  | forward hx _ => exact absurd (hR hx) (by simp)
  | rewind hx _ => exact absurd (hR hx) (by simp)
  | condense _ _ _ _ ε _ _ _ _ _ => exact congrArg (View.pull ε) hτ

/-- **`return r` is `𝔤`-closed** — the first clause of Proposition 7.5.  A
`𝔤`-rewrite maintains the number of transitions, the absence of local messages,
the equality of the delimiting views and the returned value, and those four
facts characterize the traces of `return r`. -/
theorem pureGen_closed (r : A) : Closed gRules (pureGen (Loc := Loc) (Val := Val) r) := by
  rintro τ hτ π ⟨hstep, hπ⟩
  have hlen : π.ch.toList.length = 1 := by
    rw [← hstep.length_eq (subset_refl _)]
    obtain ⟨κ, μ, -, -, rfl⟩ := hτ
    simp
  have hown : π.ch.own = ∅ :=
    hstep.own_empty gRules_subset_gcRules (pureGen_own r hτ)
  have hret : π.ret = r := by rw [← hstep.ret_eq]; exact pureGen_ret r hτ
  have hviews : π.ivw = π.fvw := by
    refine hstep.ivw_eq_fvw (subset_refl _) ?_
    obtain ⟨κ, μ, -, -, rfl⟩ := hτ
    rfl
  obtain ⟨T, hT⟩ : ∃ T, π.ch.toList = [T] := by
    match hl : π.ch.toList, hlen with
    | [T], _ => exact ⟨T, rfl⟩
  have hst := hπ.stutter_of_own_empty hown T (by rw [hT]; simp)
  refine ⟨π.ivw, T.opening, hst.2, ?_, ?_⟩
  · have : π.ch.o = T.opening := by rw [Chro.o, hT]; rfl
    rw [← this]; exact hπ.openPts
  · refine (PreTrace.mk.injEq _ _ _ _ _ _ _ _).mpr ⟨rfl, ?_, hviews.symm, hret⟩
    refine Chro.ext_toList ?_
    rw [hT, Chro.single_toList]
    exact congrArg (fun x ↦ [x]) (Transition.stutter_eq hst.1)

/-! ## `bind`

The load-bearing case.  A `𝔤`-rewrite of a concatenation splits positionally
into a `𝔤`-rewrite of each factor; the seam condition `ξ.c ⊆ η.o` is inherited
from the target chronicle, and the seam's view condition `κ ⊑ σ` survives by
Lemma 7.6 (`GData.hv_mono`). -/

/-- **`>>= f` is `𝔤`-closed when `P` and `f` are** — the second clause of
Proposition 7.5. -/
theorem bindGen_closed {P : Set (PreTrace Loc Val A)} {F : A → Set (PreTrace Loc Val B)}
    (hP : IsTraceSet P) (hF : ∀ a, IsTraceSet (F a))
    (hPc : Closed gRules P) (hFc : ∀ a, Closed gRules (F a)) :
    Closed gRules (bindGen P F) := by
  rintro π ⟨τ, υ, hseam, hτP, hυF, hview, rfl⟩ π' ⟨hstep, hπ'⟩
  have hτ : IsTrace τ := hP _ hτP
  have hυ : IsTrace υ := hF _ _ hυF
  obtain ⟨c₃, D, rfl⟩ := exists_gData (subset_refl gRules) hstep hπ'
  have hsrc : τ.ch.toList ++ υ.ch.toList = D.l ++ D.m.map D.f := D.src
  have htgt : c₃.toList = D.l.map D.h ++ D.m.map D.g := D.tgt
  suffices H : ∃ l₁ m₁ l₂ m₂ : List (Transition Loc Val),
      (∀ T ∈ m₁, D.free T) ∧ (∀ T ∈ m₂, D.free T) ∧
      τ.ch.toList = l₁ ++ m₁.map D.f ∧ υ.ch.toList = l₂ ++ m₂.map D.f ∧
      c₃.toList = (l₁.map D.h ++ m₁.map D.g) ++ (l₂.map D.h ++ m₂.map D.g) by
    obtain ⟨l₁, m₁, l₂, m₂, hf₁, hf₂, hs₁, hs₂, hc₃⟩ := H
    have hlen₁ : (l₁.map D.h ++ m₁.map D.g).length = τ.ch.toList.length := by
      rw [hs₁]; simp
    have hlen₂ : (l₂.map D.h ++ m₂.map D.g).length = υ.ch.toList.length := by
      rw [hs₂]; simp
    have hne₁ : l₁.map D.h ++ m₁.map D.g ≠ [] := by
      intro hc
      rw [hc] at hlen₁
      exact τ.ch.toList_ne_nil (List.eq_nil_of_length_eq_zero hlen₁.symm)
    have hne₂ : l₂.map D.h ++ m₂.map D.g ≠ [] := by
      intro hc
      rw [hc] at hlen₂
      exact υ.ch.toList_ne_nil (List.eq_nil_of_length_eq_zero hlen₂.symm)
    have hchain : List.IsChain Adj
        ((l₁.map D.h ++ m₁.map D.g) ++ (l₂.map D.h ++ m₂.map D.g)) := by
      rw [← hc₃]; exact c₃.chain_toList
    obtain ⟨hch₁, hch₂, -⟩ := List.isChain_append.mp hchain
    have ho₁ : (Chro.ofList _ hne₁ hch₁).toList = l₁.map D.h ++ m₁.map D.g :=
      Chro.ofList_toList _ _ _
    have ho₂ : (Chro.ofList _ hne₂ hch₂).toList = l₂.map D.h ++ m₂.map D.g :=
      Chro.ofList_toList _ _ _
    have hmem : ∀ T ∈ c₃.toList, T.WF := hπ'.wf
    -- the two halves are traces
    have htr₁ : IsTrace (⟨D.hv τ.ivw, Chro.ofList _ hne₁ hch₁, D.hv τ.fvw, τ.ret⟩ :
        PreTrace Loc Val A) := by
      refine D.mk_trace τ.ivw τ.fvw τ.ret τ.ch _ l₁ m₁ hf₁ hs₁ ho₁ hτ ?_
      intro T hT
      rw [ho₁] at hT
      exact hmem T (by rw [hc₃]; exact List.mem_append.mpr (Or.inl hT))
    have htr₂ : IsTrace (⟨D.hv υ.ivw, Chro.ofList _ hne₂ hch₂, D.hv υ.fvw, υ.ret⟩ :
        PreTrace Loc Val B) := by
      refine D.mk_trace υ.ivw υ.fvw υ.ret υ.ch _ l₂ m₂ hf₂ hs₂ ho₂ hυ ?_
      intro T hT
      rw [ho₂] at hT
      exact hmem T (by rw [hc₃]; exact List.mem_append.mpr (Or.inr hT))
    -- and are reachable from the two operands
    have hstep₁ : TStep gRules τ ⟨D.hv τ.ivw, Chro.ofList _ hne₁ hch₁, D.hv τ.fvw, τ.ret⟩ :=
      ⟨D.mk_step τ.ivw τ.fvw τ.ret τ.ch _ l₁ m₁ hf₁ hs₁ ho₁, htr₁⟩
    have hstep₂ : TStep gRules υ ⟨D.hv υ.ivw, Chro.ofList _ hne₂ hch₂, D.hv υ.fvw, υ.ret⟩ :=
      ⟨D.mk_step υ.ivw υ.fvw υ.ret υ.ch _ l₂ m₂ hf₂ hs₂ ho₂, htr₂⟩
    -- the seam condition, read off the target chronicle
    obtain ⟨S, rest, hcons⟩ := List.exists_cons_of_ne_nil hne₂
    have hseam' : (Chro.ofList _ hne₁ hch₁).c ⊆ (Chro.ofList _ hne₂ hch₂).o := by
      change listC ((Chro.ofList _ hne₁ hch₁).toList) ⊆ listO ((Chro.ofList _ hne₂ hch₂).toList)
      rw [ho₁, ho₂, hcons]
      exact chain'_listC_sub _ S rest (by rw [← hcons]; exact hchain) hne₁
    -- the view condition, by Lemma 7.6
    have hpi₁ : PointsInto τ.fvw (τ.seam υ hseam).ch.c := by
      have : (τ.seam υ hseam).ch.c = υ.ch.c := by simp
      rw [this]
      exact hτ.closePts.toPointsInto.mono (subset_trans hseam hυ.o_sub_c)
    have hpi₂ : PointsInto υ.ivw (τ.seam υ hseam).ch.c := by
      have : (τ.seam υ hseam).ch.c = υ.ch.c := by simp
      rw [this]
      exact hυ.openPts.toPointsInto.mono hυ.o_sub_c
    have hview' : D.hv τ.fvw ≤ D.hv υ.ivw := D.hv_mono _ _ hpi₁ hpi₂ hview
    refine ⟨⟨D.hv τ.ivw, Chro.ofList _ hne₁ hch₁, D.hv τ.fvw, τ.ret⟩,
      ⟨D.hv υ.ivw, Chro.ofList _ hne₂ hch₂, D.hv υ.fvw, υ.ret⟩, hseam',
      hPc _ hτP _ hstep₁, ?_, hview', ?_⟩
    · exact hFc _ _ hυF _ hstep₂
    · refine (PreTrace.mk.injEq _ _ _ _ _ _ _ _).mpr ⟨rfl, ?_, rfl, rfl⟩
      refine Chro.ext_toList ?_
      rw [Chro.append_toList, ho₁, ho₂, hc₃]
  rcases List.append_eq_append_iff.mp hsrc with ⟨as, hl, hxy⟩ | ⟨bs, hX, hm⟩
  · refine ⟨τ.ch.toList, [], as, D.m, by simp, fun T hT ↦ D.hfree T hT, by simp, hxy, ?_⟩
    rw [htgt, hl]
    simp [List.map_append, List.append_assoc]
  · obtain ⟨m₁, m₂, hmeq, hm₁, hm₂⟩ := List.map_eq_append_iff.mp hm
    refine ⟨D.l, m₁, [], m₂, fun T hT ↦ D.hfree T (by rw [hmeq]; simp [hT]),
      fun T hT ↦ D.hfree T (by rw [hmeq]; simp [hT]), by rw [hX, hm₁], by simp [hm₂], ?_⟩
    rw [htgt, hmeq]
    simp [List.map_append, List.append_assoc]

end Isotope.Elgot.RA
