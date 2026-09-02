import Isotope.Elgot.RA.Memory
import Isotope.Elgot.RA.Iteration
import Isotope.Elgot.RA.Parallel

/-!
# Tools for reasoning about refinement in the release/acquire model

Support for `Isotope/Elgot/RA/Opt/`, which proves program transformations sound
in Dvir, Kammar and Lahav's models (`release-acquire`, TOPLAS 47(2):7).

## The direction convention, which is the easiest thing to get wrong here

`P ≤ Q` unfolds to `P.traces ⊆ Q.traces`.  The paper writes `M ↠ N` for "the
transformation replacing `M` by `N` is validated", and says (journal §3.3, p.11)
that this holds exactly when `⟦N⟧ ⊑ ⟦M⟧`.  So

> `P ≤ Q` validates the transformation `Q ↠ P`

— the *target* of the transformation has the *smaller* trace set.  Every
statement in `Opt/` is checked against this reading in its docstring.

## What is here

* `Comp.le_of_gen_subset_closure`, the one-line consequence of the closure being
  a monotone idempotent operator: to refine one closed computation into another
  it is enough to push the *generating* set of the source into the closure of the
  generating set of the target.  Unlike the paper's Deferral of Closure this
  needs no hypothesis on the rule set, but it also does not let one rewrite the
  *target*'s generating set.
* `Comp.approx_mono` and `Comp.iterate_mono`: iteration is monotone.  With the
  existing `Comp.bind_mono` and `Comp.par_mono` this says that refinement is a
  **precongruence** for every construct of the model — `>>=`, `∥∥∥` and the
  iteration operator — which is what makes the transformations of
  `Opt/Sequential.lean` usable inside larger programs.  It is *not* a
  substitute for the paper's adequacy theorem, which is not formalized here:
  precongruence is a statement about the denotational model alone.
* `mem_pure_of_own_empty`: a trace with no local messages *is* a trace of
  `return` of its own returned value.  This is the converse of
  `Closure.Refines.own_empty` and the engine of the read-elimination results.
* `Comp.traces_bind_pure_comp`: `P >>= (return ∘ f)` is `P` with its returned
  values relabelled along `f`.  Available for every `𝔠 ⊆ R ⊆ 𝔤𝔠 ∪ {Ti, Ab}`,
  i.e. wherever the unit laws hold, and *proved by the unit-law argument* rather
  than derived from them, so that it is available at `gcTiAbRules` too.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {R : RuleSet} {A B : Type u}

/-! ## Refining through generating sets -/

/-- To refine one closed computation into another it suffices to push the
generating set of the source into the closure of the generating set of the
target.  Valid at every rule set: `closure R` is monotone and idempotent. -/
theorem Comp.le_of_gen_subset_closure {S T : Set (PreTrace Loc Val A)}
    (hS : IsTraceSet S) (hT : IsTraceSet T) (h : S ⊆ closure R T) :
    Comp.close R S hS ≤ Comp.close R T hT := by
  rw [Comp.le_def, Comp.traces_close, Comp.traces_close]
  exact closure_subset_of_closed (closure_closed R T) h

/-- A computation is below any closed computation containing its generating
set. -/
theorem Comp.close_le {S : Set (PreTrace Loc Val A)} (hS : IsTraceSet S)
    {Q : Comp R Loc Val A} (h : S ⊆ Q.traces) : Comp.close R S hS ≤ Q :=
  closure_subset_of_closed Q.closed h

/-! ## Iteration is monotone -/

namespace Comp

/-- Each finite unrolling is monotone in the loop body. -/
theorem approx_mono {f g : A → Comp R Loc Val (B ⊕ A)} (h : ∀ a, f a ≤ g a) :
    ∀ (n : ℕ) (a : A), approx f n a ≤ approx g n a
  | 0, _ => le_refl _
  | n + 1, a => by
      rw [approx_succ, approx_succ]
      refine bind_mono (h a) (fun s ↦ ?_)
      cases s with
      | inl b => exact le_refl _
      | inr a' => exact approx_mono h n a'

/-- **Iteration is monotone.**  Together with `Comp.bind_mono` and
`Comp.par_mono` this makes refinement a precongruence for the whole language of
the model.  Not in the paper, which has no iteration operator at all (journal
§4). -/
theorem iterate_mono {f g : A → Comp R Loc Val (B ⊕ A)} (h : ∀ a, f a ≤ g a) (a : A) :
    iterate f a ≤ iterate g a :=
  iterate_le (fun n ↦ le_trans (approx_mono h n a) (approx_le_iterate g n a))

/-- `iter` is monotone: the `Iterate`-instance spelling of `iterate_mono`. -/
theorem iter_mono {f g : A → Comp R Loc Val (B ⊕ A)} (h : ∀ a, f a ≤ g a) (a : A) :
    iter f a ≤ iter g a := iterate_mono h a

/-- Loop bodies that agree give equal loops. -/
theorem iterate_congr {f g : A → Comp R Loc Val (B ⊕ A)} (h : ∀ a, f a = g a) :
    iterate f = iterate g := by
  funext a; exact congrFun (congrArg iterate (funext h)) a

end Comp

/-! ## Traces with no local messages are traces of `return` -/

/-- **A trace with no local messages is a trace of `return`** of its own
returned value.  Local messages are the only intensional record a chronicle
keeps of what the computation itself did, so a computation that leaves none is
indistinguishable from `return`.

This is the converse of `Refines.own_empty` and is the mechanism behind
irrelevant-read elimination.  Original: the paper never states it. -/
theorem mem_pure_of_own_empty (hSt : Rule.St ∈ R) (hFw : Rule.Fw ∈ R)
    {π : PreTrace Loc Val A} (hπ : IsTrace π) (hown : π.ch.own = ∅) :
    π ∈ (Pure.pure π.ret : Comp R Loc Val A).traces := by
  have hfirst : π.ch.first = ⟨π.ch.o, π.ch.o⟩ :=
    Transition.stutter_eq (hπ.stutter_of_own_empty hown π.ch.first π.ch.first_mem).1
  set τ : PreTrace Loc Val A :=
    ⟨π.ivw, Chro.single ⟨π.ch.o, π.ch.o⟩, π.ivw, π.ret⟩ with hτdef
  have hτg : τ ∈ pureGen (Loc := Loc) (Val := Val) π.ret :=
    ⟨π.ivw, π.ch.o, hπ.wf_o, hπ.openPts, rfl⟩
  have hτ : IsTrace τ := pureGen_isTrace π.ret τ hτg
  have hlist : π.ch.toList = τ.ch.toList ++ π.ch.rest := by
    rw [hτdef]
    simp only [Chro.single_toList, List.singleton_append]
    conv_lhs => rw [Chro.toList, hfirst]
  have hst : ∀ T ∈ π.ch.rest, T.opening = T.closing ∧ WellFormed T.opening := fun T hT ↦
    hπ.stutter_of_own_empty hown T (by rw [Chro.toList]; exact List.mem_cons_of_mem _ hT)
  have hcl : ∀ T ∈ π.ch.rest, PointsDownInto τ.fvw T.opening := fun T hT ↦
    hπ.openPts.mono (hπ.o_sub_mem_of_own_empty hown
      (by rw [Chro.toList]; exact List.mem_cons_of_mem _ hT))
  have hgrow : Refines R τ ⟨π.ivw, π.ch, π.ivw, π.ret⟩ :=
    stutter_suffix hSt hτ π.ch.rest π.ch hlist hst hcl
  refine (closure_closed R _).mem_of_refines (subset_closure hτg) (hgrow.tail ?_)
  exact ⟨Step.forward hFw hπ.mono, hπ⟩

/-! ## Binding with `return ∘ f` is relabelling -/

/-- **`P >>= (return ∘ f)` is `P` with its returned values relabelled.**  Valid
for every `𝔠 ⊆ R ⊆ 𝔤𝔠 ∪ {Ti, Ab}` — the whole range on which the unit laws hold
(`Isotope/Elgot/RA/Monad.lean`), including the Concrete model `C`.  The proof is
the unit-law argument run with a relabelled returned value, not a consequence of
the unit laws, so it is available at `gcTiAbRules`, where associativity is not.

Original: the paper proves no monad law, hence nothing of this kind. -/
theorem Comp.traces_bind_pure_comp (hcR : cRules ⊆ R) (hRg : R ⊆ gcTiAbRules)
    (P : Comp R Loc Val A) (f : A → B) :
    (P >>= fun a ↦ (Pure.pure (f a) : Comp R Loc Val B)).traces
      = closure R (PreTrace.mapRet f '' P.traces) := by
  rw [Comp.traces_bind]
  apply Set.Subset.antisymm
  · refine closure_subset_of_closed (closure_closed R _) ?_
    rintro π ⟨τ, υ, h, hτ, hυ, hs, rfl⟩
    have hτ' : IsTrace τ := P.isTrace _ hτ
    have hυ' : IsTrace υ := (pureGen_isTrace (f τ.ret)).closure _ hυ
    have hown : υ.ch.own = ∅ := closure_pureGen_own hRg (f τ.ret) hυ
    have hret : υ.ret = f τ.ret := closure_pureGen_ret (f τ.ret) hυ
    have hmap : IsTrace (τ.mapRet f) := hτ'.mapRet
    have hcl : ∀ T ∈ υ.ch.toList, PointsDownInto (τ.mapRet f).fvw T.opening := fun T hT ↦
      hτ'.closePts.mono (subset_trans h (hυ'.o_sub_mem_of_own_empty hown hT))
    have hgrow : Refines R (τ.mapRet f)
        ⟨τ.ivw, τ.ch.append υ.ch h, τ.fvw, f τ.ret⟩ :=
      stutter_suffix (hcR (by simp)) hmap υ.ch.toList (τ.ch.append υ.ch h) (by simp)
        (fun T hT ↦ hυ'.stutter_of_own_empty hown T hT) hcl
    refine ⟨τ.mapRet f, ⟨τ, hτ, rfl⟩, hgrow.tail ⟨?_, hτ'.append hυ' hs h⟩⟩
    have hseam : τ.seam υ h = ⟨τ.ivw, τ.ch.append υ.ch h, υ.fvw, f τ.ret⟩ := by
      rw [PreTrace.seam, hret]
    rw [hseam]
    exact Step.forward (hcR (by simp)) (le_trans hs hυ'.mono)
  · refine closure_subset_of_closed (closure_closed R _) ?_
    rintro π ⟨τ, hτ, rfl⟩
    have hτ' : IsTrace τ := P.isTrace _ hτ
    set υ : PreTrace Loc Val B :=
      ⟨τ.fvw, Chro.single ⟨τ.ch.c, τ.ch.c⟩, τ.fvw, f τ.ret⟩ with hυdef
    have hυg : υ ∈ pureGen (Loc := Loc) (Val := Val) (f τ.ret) :=
      ⟨τ.fvw, τ.ch.c, hτ'.wf_c, hτ'.closePts, rfl⟩
    have hseam : τ.ch.c ⊆ υ.ch.o := by rw [hυdef]; simp
    have hmem : τ.seam υ hseam
        ∈ bindGen P.traces (fun a ↦ (Pure.pure (f a) : Comp R Loc Val B).traces) :=
      ⟨τ, υ, hseam, hτ, subset_closure hυg, le_refl _, rfl⟩
    refine (closure_closed R _).mem_of_refines (subset_closure hmem) (Refines.single ?_)
    obtain ⟨l, T, hl, hc⟩ := listC_concat τ.ch.toList τ.ch.toList_ne_nil
    refine ⟨Step.chro (hcR (by simp))
      (ChroStep.mumble _ _ l [] T.opening τ.ch.c τ.ch.c ?_ ?_), hτ'.mapRet⟩
    · simp only [Chro.append_toList, hυdef, Chro.single_toList]
      rw [hl]
      simp only [List.append_assoc, List.cons_append, List.nil_append]
      rw [show T = ⟨T.opening, T.closing⟩ from rfl, ← hc]
      rfl
    · rw [hl]
      have hTc : τ.ch.c = T.closing := hc
      rw [hTc]

end Isotope.Elgot.RA
