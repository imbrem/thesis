import Isotope.Elgot.RA.Parallel

/-!
# Laws relating `∥∥∥` to `>>=`: thread inlining and Generalized Sequencing

Two of the laws Dvir, Kammar and Lahav (`release-acquire`, TOPLAS 47(2):7)
state for `∥∥∥`, both about its interaction with `>>=`.

## What kind of operation `∥∥∥` is, and why there is no "Kleisli" form

`∥∥∥` has type `T X × T Y → T (X × Y)` (journal §7.1, p.27).  It is **not** a
Kleisli map `X → T Y`, and it is not derivable from `Monad (Comp R Loc Val)`:
it is a *second*, concurrent tensor, extra algebraic structure on `T` in Moggi's
style, one component per effect construct.  Consequently:

* it composes with `>>=` only through the laws below, not through `bind`;
* the interaction with the *sequential* tensor is an **inclusion, not an
  equality** — the interchange of a lax monoidal structure, not a duoidal one;
* the sequential pairing `⟨M,N⟩` and the concurrent `M ∥ N` are related in one
  direction only (`Comp.seqPair_le_par`), which is exactly the paper's
  `M ∥ N ↠ ⟨M,N⟩`.

## Thread inlining, `M ∥ N ↠ ⟨M,N⟩`

**Claimed by the paper, proved nowhere.**  Fig. 3 (journal p.12) and Table 3
(p.44) list "Sequencing" among the validated program transformations, and p.45
stresses it as the RA-vs-x86-TSO discriminator ("sequencing, a.k.a.
thread-inlining, is unsound under x86-TSO … but sound under RA"), but there is
no proposition, no proof and no proof sketch for it in either the 85-page
journal version or the 80-page ESOP full version.  `pairGen_subset_parGen`
and `Comp.seqPair_le_par` are therefore **original work, not a port**.

The mathematical content is `pairGen_subset_parGen`: a *bind seam* is one of the
interleavings — the one that runs the left thread to completion first — and the
left thread's initial view already points downwards into the right thread's
opening memory, because `α₁ ↠ ξ₁.o ⊆ ξ₁.c ⊆ ξ₂.o`.  So the right operand can be
`Rewind`ed to start from `α₁` too, after which `inf_{ξ.o}{α₁,α₁} = α₁` and
`sup{ω₁,ω₂} = ω₂`.

## Generalized Sequencing, the exchange law

**Proposition E.1** (journal p.58; ESOP full version Proposition C.1), proved
there:

> If `Γ ⊢ M₁ : A₁`; `Γ ⊢ N₁ : B₁`; `Γ, a:A₀ ⊢ M₂ : A₂`; and `Γ, b:B₀ ⊢ N₂ : B₂`:
> `⟦(let a = M₁ in M₂) ∥ (let b = N₁ in N₂)⟧ᶜ ⊇ ⟦match M₁ ∥ N₁ with ⟨a,b⟩. M₂ ∥ N₂⟧ᶜ`

semantically `(P₁ ||| Q₁) >>= (λ⟨a,b⟩. F a ||| G b) ⊆ (P₁ >>= F) ||| (Q₁ >>= G)`.

⚠ **Erratum in the paper.**  The proof of E.1 says "denoting the resulting sets
`P` and `Q`.  Thus we require `P ⊆ Q`" and then proves `Q ⊆ P`.  The proof, not
the sentence, is authoritative: it is corroborated by the orientation of `↠`
fixed at journal p.11 (`M ↠ N` is validated by `⟦N⟧ ⊆ ⟦M⟧`) and by Props E.2/E.3.
The Lean statement below is unambiguous and should be read in place of the
paper's sentence.

`bindGen_parGen_subset` is a **stronger and shorter** result than the paper's:
it needs no closure at all, no rule-set hypothesis, and no appeal to Deferral of
Closure.  Every seam of a parallel composition splits into the two component
seams by `IsInfMem.lb`, and `Interleave.appendCompat` reassembles the shuffle.
The paper's proof (p.58) works inside the closed sets and lists Deferral of
Closure among its ingredients.
-/

universe u

namespace Isotope.Elgot.RA

open Isotope.Elgot (Interleave)

variable {Loc Val : Type} {R : RuleSet} {A B C D : Type u}

/-! ## Thread inlining -/

/-- The traces of the *sequential pairing* `⟨M,N⟩`: a bind seam whose returned
value is the pair of the two operands' returned values. -/
def pairGen (P : Set (PreTrace Loc Val A)) (Q : Set (PreTrace Loc Val B)) :
    Set (PreTrace Loc Val (A × B)) :=
  {π | ∃ (τ : PreTrace Loc Val A) (υ : PreTrace Loc Val B) (h : τ.ch.c ⊆ υ.ch.o),
    τ ∈ P ∧ υ ∈ Q ∧ τ.fvw ≤ υ.ivw ∧ π = (τ.seam υ h).mapRet (fun b ↦ (τ.ret, b))}

/-- **Thread inlining**, `M ∥ N ↠ ⟨M,N⟩` (Fig. 3, journal p.12; Table 3, p.44):
every sequential pairing of two traces is one of their interleavings.  Original
work — the paper claims the transformation and never proves it. -/
theorem pairGen_subset_parGen (hRw : Rule.Rw ∈ R) {P : Set (PreTrace Loc Val A)}
    {Q : Set (PreTrace Loc Val B)} (hP : IsTraceSet P) (hQ : IsTraceSet Q)
    (hQc : Closed R Q) : pairGen P Q ⊆ parGen P Q := by
  rintro π ⟨τ, υ, h, hτ, hυ, hs, rfl⟩
  have hτ' : IsTrace τ := hP _ hτ
  have hυ' : IsTrace υ := hQ _ hυ
  have hαle : τ.ivw ≤ υ.ivw := le_trans hτ'.mono hs
  -- the right operand, rewound to start from the left operand's initial view
  have hpd : PointsDownInto τ.ivw υ.ch.o :=
    hτ'.openPts.mono (subset_trans hτ'.o_sub_c h)
  have hυ'' : IsTrace (⟨τ.ivw, υ.ch, υ.fvw, υ.ret⟩ : PreTrace Loc Val B) :=
    { wf := hυ'.wf
      openPts := hpd
      mono := le_trans hαle hυ'.mono
      closePts := hυ'.closePts
      own := by
        intro ν hν
        obtain ⟨h1, h2, h3⟩ := hυ'.own ν hν
        exact ⟨le_trans hαle h1, h2, lt_of_le_of_lt (hαle ν.lc) h3⟩ }
  have hmem : (⟨τ.ivw, υ.ch, υ.fvw, υ.ret⟩ : PreTrace Loc Val B) ∈ Q :=
    hQc υ hυ _ ⟨Step.rewind hRw hαle, hυ''⟩
  refine ⟨τ, hτ, _, hmem, ChroInterleave.append τ.ch υ.ch h, ?_, ?_, rfl⟩
  · exact isInfMem_pair_self (μ := (τ.ch.append υ.ch h).o) hτ'.openPts
  · change υ.fvw = τ.fvw ⊔ υ.fvw
    exact (sup_eq_right.mpr (le_trans hs hυ'.mono)).symm

/-- The sequential pairing is a bind followed by a `return` of the pair: the
trailing `pure` contributes one stutter transition, removed by `Mumble` and a
`Forward`, exactly as in `closure_bindGen_pureGen_right`. -/
theorem bindGen_bindGen_pureGen_subset (hcR : cRules ⊆ R) (hRg : R ⊆ gcRules)
    {P : Set (PreTrace Loc Val A)} {Q : Set (PreTrace Loc Val B)}
    (hP : IsTraceSet P) (hQ : IsTraceSet Q) :
    bindGen P (fun a ↦ bindGen Q (fun b ↦ closure R (pureGen (a, b))))
      ⊆ closure R (pairGen P Q) := by
  rintro π ⟨τ, ζ, hζseam, hτ, ⟨υ, w, hw, hυ, hwmem, hs2, rfl⟩, hs, rfl⟩
  have h₁ : τ.ch.c ⊆ υ.ch.o := by simpa using hζseam
  have hs' : τ.fvw ≤ υ.ivw := by simpa using hs
  have hτ' : IsTrace τ := hP _ hτ
  have hυ' : IsTrace υ := hQ _ hυ
  have hw' : IsTrace w := (pureGen_isTrace _).closure _ hwmem
  have hown : w.ch.own = ∅ := closure_pureGen_own (hRg.trans gcRules_subset_gcTiAbRules) _ hwmem
  have hret : w.ret = (τ.ret, υ.ret) := closure_pureGen_ret _ hwmem
  set ρ : PreTrace Loc Val (A × B) := (τ.seam υ h₁).mapRet (fun b ↦ (τ.ret, b)) with hρdef
  have hρ : IsTrace ρ := (hτ'.append hυ' hs' h₁).mapRet
  have hwx : ρ.ch.c ⊆ w.ch.o := by
    change (τ.ch.append υ.ch h₁).c ⊆ w.ch.o
    simpa using hw
  have hst : ∀ T ∈ w.ch.toList, T.opening = T.closing ∧ WellFormed T.opening :=
    fun T hT ↦ hw'.stutter_of_own_empty hown T hT
  have hcl : ∀ T ∈ w.ch.toList, PointsDownInto ρ.fvw T.opening := by
    intro T hT
    exact hυ'.closePts.mono (subset_trans hw (hw'.o_sub_mem_of_own_empty hown hT))
  have hstut := stutter_suffix (R := R) (hcR (by simp)) hρ w.ch.toList
    (ρ.ch.append w.ch hwx) (by simp) hst hcl
  have hfw : ρ.fvw ≤ w.fvw := le_trans hs2 hw'.mono
  have hc2 : (τ.ch.append υ.ch h₁).append w.ch hwx
      = τ.ch.append (υ.ch.append w.ch hw) hζseam :=
    Chro.append_assoc τ.ch υ.ch w.ch h₁ hw
  have heq : (⟨ρ.ivw, ρ.ch.append w.ch hwx, w.fvw, ρ.ret⟩ : PreTrace Loc Val (A × B))
      = τ.seam (υ.seam w hw) hζseam := by
    change (⟨τ.ivw, (τ.ch.append υ.ch h₁).append w.ch hwx, w.fvw, (τ.ret, υ.ret)⟩ :
      PreTrace Loc Val (A × B)) = _
    rw [hc2, ← hret]
    rfl
  have hmid : IsTrace (τ.seam (υ.seam w hw) hζseam) :=
    hτ'.append (hυ'.append hw' hs2 hw) hs hζseam
  refine ⟨ρ, ⟨τ, υ, h₁, hτ, hυ, hs', rfl⟩, ?_⟩
  rw [← heq]
  exact hstut.tail ⟨Step.forward (hcR (by simp)) hfw, by rw [heq]; exact hmid⟩

/-! ## The exchange law -/

/-- **Proposition E.1, Generalized Sequencing** (journal p.58): sequencing
inside a parallel composition refines the parallel composition of the
sequencings.  This is an *inclusion*, and it is one-sided: `∥∥∥` and `>>=` do
not commute.

Stronger than the paper's statement: no closure, and no hypothesis on the rule
set.  The seam of the parallel composition splits into the two component seams
because `inf_{ξ'.o}{α₂,κ₂}` lies below both `α₂` and `κ₂`; the two component
seams' memory conditions come from `ξᵢ.c ⊆ ξ.c` and `ξ'.o ⊆ ξᵢ'.o`; and
`Interleave.appendCompat` reassembles `ξξ' ∈ (ξ₁ξ₂) ∥ (η₁η₂)`. -/
theorem bindGen_parGen_subset {P : Set (PreTrace Loc Val A)}
    {Q : Set (PreTrace Loc Val B)} {F : A → Set (PreTrace Loc Val C)}
    {G : B → Set (PreTrace Loc Val D)} (hP : IsTraceSet P) (hQ : IsTraceSet Q)
    (hF : ∀ a, IsTraceSet (F a)) (hG : ∀ b, IsTraceSet (G b)) :
    bindGen (parGen P Q) (fun p ↦ parGen (F p.1) (G p.2))
      ⊆ parGen (bindGen P F) (bindGen Q G) := by
  rintro π ⟨ζ, ζ', hseam, ⟨τ₁, hτ₁, υ₁, hυ₁, hint, hinf, hfvw, hret⟩,
    ⟨τ₂, hτ₂, υ₂, hυ₂, hint', hinf', hfvw', hret'⟩, hs, rfl⟩
  have hτ₁' : IsTrace τ₁ := hP _ hτ₁
  have hυ₁' : IsTrace υ₁ := hQ _ hυ₁
  have hwf : ∀ T ∈ ζ.ch.toList, T.WF := hint.wf hτ₁'.wf hυ₁'.wf
  have hτ₂F : τ₂ ∈ F τ₁.ret := by
    have h : τ₂ ∈ F ζ.ret.1 := hτ₂
    rw [hret] at h; exact h
  have hυ₂G : υ₂ ∈ G υ₁.ret := by
    have h : υ₂ ∈ G ζ.ret.2 := hυ₂
    rw [hret] at h; exact h
  have hτ₂' : IsTrace τ₂ := hF _ _ hτ₂F
  have hυ₂' : IsTrace υ₂ := hG _ _ hυ₂G
  have hwf' : ∀ T ∈ ζ'.ch.toList, T.WF := hint'.wf hτ₂'.wf hυ₂'.wf
  -- the two component seams
  have hcs₁ : τ₁.ch.c ⊆ τ₂.ch.o :=
    subset_trans (hint.c_sub_left hwf) (subset_trans hseam (hint'.o_sub_left hwf'))
  have hcs₂ : υ₁.ch.c ⊆ υ₂.ch.o :=
    subset_trans (hint.c_sub_right hwf) (subset_trans hseam (hint'.o_sub_right hwf'))
  have hvs₁ : τ₁.fvw ≤ τ₂.ivw :=
    le_trans (le_trans (by rw [hfvw]; exact le_sup_left) hs) (hinf'.lb _ (by simp))
  have hvs₂ : υ₁.fvw ≤ υ₂.ivw :=
    le_trans (le_trans (by rw [hfvw]; exact le_sup_right) hs) (hinf'.lb _ (by simp))
  refine ⟨τ₁.seam τ₂ hcs₁, ⟨τ₁, τ₂, hcs₁, hτ₁, hτ₂F, hvs₁, rfl⟩,
    υ₁.seam υ₂ hcs₂, ⟨υ₁, υ₂, hcs₂, hυ₁, hυ₂G, hvs₂, rfl⟩,
    ?_, ?_, ?_, ?_⟩
  · exact Interleave.appendCompat hint.toInterleave hint'.toInterleave
  · change IsInfMem ζ.ch.o {τ₁.ivw, υ₁.ivw} ζ.ivw
    exact hinf
  · change ζ'.fvw = (τ₁.seam τ₂ hcs₁).fvw ⊔ (υ₁.seam υ₂ hcs₂).fvw
    exact hfvw'
  · change ζ'.ret = ((τ₁.seam τ₂ hcs₁).ret, (υ₁.seam υ₂ hcs₂).ret)
    exact hret'

/-! ## The unit law, one direction only

Table 3 (journal p.44) claims "Symmetric-Monoidal Laws, e.g.
`M ∥ N ↠ match N ∥ M with ⟨b,a⟩.⟨a,b⟩`" and the Fig. 3 caption (p.12) claims
"all symmetric-monoidal laws with the binary operator `∥` and the unit `⟨⟩`",
with no proposition, proof or sketch anywhere.  Of the unit law we prove the
direction `P ⊆ P ||| return r` (modulo pairing the returned value): the pure
operand contributes a single stutter `⟨ξ.o, ξ.o⟩`, scheduled first, and `Mumble`
absorbs it into the first transition of `P`'s trace.

⚠ **The converse is not proved and was not attempted.**  It would have to
remove, from an arbitrary shuffle, the stutters contributed by an arbitrary
member of `(return r)★`; `Mumble` merges `⟨μ,ρ⟩⟨ρ,θ⟩` only when the memories
match exactly, whereas chronicle adjacency gives only `⊆`.  Associativity of
`∥∥∥` is likewise **neither proved nor attempted**; see the honest boundary in
`Isotope/Elgot/RA.lean`. -/

/-- Every trace of `P`, with its returned value paired with `r`, is a trace of
`P ||| return r`: the pure operand's single stutter is scheduled first and
mumbled away.  Original work. -/
theorem mapRet_image_subset_parGen_pureGen (hMu : Rule.Mu ∈ R)
    {P : Set (PreTrace Loc Val A)} (hP : IsTraceSet P) (r : B) :
    PreTrace.mapRet (fun a ↦ (a, r)) '' P ⊆ closure R (parGen P (pureGen r)) := by
  rintro _ ⟨τ, hτ, rfl⟩
  have hτ' : IsTrace τ := hP _ hτ
  have hh : (Chro.single (⟨τ.ch.o, τ.ch.o⟩ : Transition Loc Val)).c ⊆ τ.ch.o := by simp
  refine ⟨⟨τ.ivw, (Chro.single (⟨τ.ch.o, τ.ch.o⟩ : Transition Loc Val)).append τ.ch hh,
      τ.fvw, (τ.ret, r)⟩,
    ⟨τ, hτ, ⟨τ.ivw, Chro.single ⟨τ.ch.o, τ.ch.o⟩, τ.ivw, r⟩,
      ⟨τ.ivw, τ.ch.o, hτ'.wf_o, hτ'.openPts, rfl⟩, ?_, ?_, ?_, rfl⟩, ?_⟩
  · change Interleave τ.ch.toList [(⟨τ.ch.o, τ.ch.o⟩ : Transition Loc Val)]
      ([(⟨τ.ch.o, τ.ch.o⟩ : Transition Loc Val)] ++ τ.ch.toList)
    exact (Interleave.append _ _).swap
  · change IsInfMem τ.ch.o {τ.ivw, τ.ivw} τ.ivw
    exact isInfMem_pair_self hτ'.openPts
  · change τ.fvw = τ.fvw ⊔ τ.ivw
    exact (sup_eq_left.mpr hτ'.mono).symm
  · refine Refines.single ⟨Step.chro hMu (ChroStep.mumble _ _ [] τ.ch.rest τ.ch.o τ.ch.o
      τ.ch.first.closing ?_ ?_), hτ'.mapRet⟩
    · simp only [Chro.append_toList, Chro.single_toList, List.nil_append,
        List.singleton_append]
      rfl
    · simp only [List.nil_append]
      rfl

/-! ## At the level of computations

Both corollaries are stated at `R = 𝔠`, because both need Deferral of Closure at
the bind seam (`closure_bindGen_closure_left/right`), which
`Isotope/Elgot/RA/Monad.lean` proves only for `R ⊆ 𝔠` — the `𝔤` rules replace
messages in the closing memory of the left operand, so the seam condition is not
transported backwards along a rewrite.  The generating-set statements above hold
much more generally: `bindGen_parGen_subset` for every rule set, and
`pairGen_subset_parGen` whenever `Rw ∈ R`. -/

namespace Comp

/-- The sequential pairing `⟨M,N⟩ := let a = M in let b = N in ⟨a,b⟩`. -/
def seqPair (P : Comp R Loc Val A) (Q : Comp R Loc Val B) : Comp R Loc Val (A × B) :=
  P >>= fun a ↦ Q >>= fun b ↦ pure (a, b)

/-- **Thread inlining**, `M ∥ N ↠ ⟨M,N⟩` (Fig. 3, journal p.12; Table 3, p.44).
Original work: the paper claims this transformation and proves it nowhere. -/
theorem seqPair_le_par (P : Comp cRules Loc Val A) (Q : Comp cRules Loc Val B) :
    P.seqPair Q ≤ P.par Q := by
  rw [le_def, traces_par]
  change closure cRules (bindGen P.traces
      (fun a ↦ closure cRules (bindGen Q.traces (fun b ↦ closure cRules (pureGen (a, b))))))
    ⊆ _
  rw [closure_bindGen_closure_right (subset_refl _) P.isTrace
    (fun a ↦ bindGen_isTrace Q.isTrace (fun b ↦ (pureGen_isTrace _).closure))]
  refine closure_subset_of_closed (closure_closed _ _) ?_
  refine subset_trans (bindGen_bindGen_pureGen_subset (subset_refl _)
    cRules_subset_gcRules P.isTrace Q.isTrace) ?_
  exact closure_subset_of_closed (closure_closed _ _)
    (subset_trans (pairGen_subset_parGen (by simp) P.isTrace Q.isTrace Q.closed)
      subset_closure)

/-- `P ⊆ P ||| return r`, the reachable half of the unit law, at every rule set
containing `Mumble`.  Original work; the converse is not proved. -/
theorem mapRet_image_subset_par_pure (hMu : Rule.Mu ∈ R) (P : Comp R Loc Val A) (r : B) :
    PreTrace.mapRet (fun a ↦ (a, r)) '' P.traces ⊆ (P.par (Pure.pure r)).traces := by
  refine subset_trans (mapRet_image_subset_parGen_pureGen hMu P.isTrace r) ?_
  rw [traces_par, traces_pure]
  exact closure_mono (parGen_mono (subset_refl _) subset_closure)

/-- The same on the other side, by Symmetry. -/
theorem mapRet_image_subset_pure_par (hMu : Rule.Mu ∈ R) (P : Comp R Loc Val A) (r : B) :
    PreTrace.mapRet (fun a ↦ (r, a)) '' P.traces
      ⊆ ((Pure.pure r : Comp R Loc Val B).par P).traces := by
  rintro _ ⟨τ, hτ, rfl⟩
  rw [par_swap]
  exact ⟨(τ.mapRet (fun a ↦ (a, r))),
    mapRet_image_subset_par_pure hMu P r ⟨τ, hτ, rfl⟩, rfl⟩

/-- **Proposition E.1, Generalized Sequencing** (journal p.58), for the
`𝔠`-model.  The interaction of the concurrent tensor `∥∥∥` with the sequential
`>>=` is an inclusion, never an equality. -/
theorem bind_par_le_par_bind (P : Comp cRules Loc Val A) (Q : Comp cRules Loc Val B)
    (F : A → Comp cRules Loc Val C) (G : B → Comp cRules Loc Val D) :
    (P.par Q >>= fun p ↦ (F p.1).par (G p.2)) ≤ (P >>= F).par (Q >>= G) := by
  rw [le_def, traces_bind, traces_par]
  have hFG : ∀ p : A × B, IsTraceSet (parGen (F p.1).traces (G p.2).traces) :=
    fun p ↦ parGen_isTrace (F p.1).isTrace (G p.2).isTrace
  change closure cRules (bindGen (closure cRules (parGen P.traces Q.traces))
      (fun p ↦ closure cRules (parGen (F p.1).traces (G p.2).traces))) ⊆ _
  rw [closure_bindGen_closure_right (subset_refl _)
      (parGen_isTrace P.isTrace Q.isTrace).closure hFG,
    closure_bindGen_closure_left (subset_refl _) (parGen_isTrace P.isTrace Q.isTrace) hFG]
  refine closure_subset_of_closed (closure_closed _ _) ?_
  refine subset_trans (bindGen_parGen_subset P.isTrace Q.isTrace
    (fun a ↦ (F a).isTrace) (fun b ↦ (G b).isTrace)) ?_
  exact subset_trans (parGen_mono subset_closure subset_closure) subset_closure

end Comp

end Isotope.Elgot.RA
