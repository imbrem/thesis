import Isotope.Elgot.Brookes.SeqCst.Litmus
import Isotope.Elgot.RA.Opt.StoreBuffering

/-!
# Separating sequential consistency from release/acquire

A two-sided theorem about the *same* transformation in two of this
repository's memory models:

* the Brookes model of **sequential consistency**
  (`Isotope/Elgot/Brookes/SeqCst.lean`), and
* the **release/acquire** models of Dvir, Kammar and Lahav
  (`Isotope/Elgot/RA/`, TOPLAS 47(2):7).

## The transformation

Let `SB` be the store-buffering program

```
SB  :=  (x := v₁ ; y?)  ∥  (y := v₁ ; x?)
```

and let `assert⟨v₀,v₀⟩` be the post-processing that diverges on the outcome
`⟨v₀,v₀⟩` and is the identity otherwise.  The transformation under study is

```
S  :=  SB ; assert⟨v₀,v₀⟩          ↠          T  :=  SB
```

*"delete an assertion that can never fire."*

`⊥` is the denotation of a real program, not a semantic gadget: in **both**
models the always-diverging loop denotes the empty trace set — see
`Isotope.Elgot.Brookes.iter_forever` and `Isotope.Elgot.RA.iter_diverge`.  So
`S` and `T` are both expressible.

## Direction

A transformation `S ↠ T` is sound in a model exactly when `⟦T⟧ ⊆ ⟦S⟧`.  The
*smaller program text* `T` therefore carries the *larger* trace set, and the
inclusion to be checked is the non-trivial one.

## The two halves

* **Sound under sequential consistency** (`sc_assert_elim_sound`): for every
  interference-free execution from a store in which `x` and `y` both hold `v₀`,
  every execution of `T` is an execution of `S`.
* **Unsound under release/acquire** (`ra_assert_elim_unsound`): an explicit
  trace of `T` is provably not a trace of `S` — at every rule set containing
  `Mumble`, so at the paper's Concrete model `C` and its Abstract model `A`
  alike.

## Why this is a fair comparison, and what it does *not* say

The two models have incomparable states — a store `Loc → Val` on one side, a
set of timestamped messages plus a view on the other — so there is no functor
between them and none is attempted.  What the two halves share is the *shape of
the observation*: a whole-program, interference-free execution from the model's
initial state.

* On the sequentially consistent side that is the hypothesis `Seq μ t σ`: every
  gap between successive rely-guarantee pairs is closed.  The hypothesis cannot
  be dropped.  In the open, compositional order the sequentially consistent
  model *also* admits `⟨v₀,v₀⟩`, because the environment may restore `x`.
* On the release/acquire side it is the chronicle being a **single transition**
  `⟨μ₀, μ₀ ⊎ {ν_x, ν_y}⟩` out of the paper's initial memory — which is exactly
  the shape the paper's own Soundness theorem (journal Thm. 8.12, p.42) assigns
  to a whole-program evaluation.  The counterexample therefore lies inside the
  restricted class, so the restriction on the sequentially consistent half is
  not what makes the two halves differ.

Everything proved here is **denotational**.  "Release/acquire admits store
buffering" as an *operational* fact would need the adequacy theorem, which is
not formalized in this repository, and the paper's operational semantics is not
formalized at all.  The honest statement is the denotational one, and it agrees
with the paper's own Example 5.3 (journal p.19).

Do **not** read this as "sequential consistency validates more transformations
than release/acquire".  That is a non-sequitur: soundness of `S ↠ T` is
`⟦T⟧ ⊆ ⟦S⟧`, and weakening a model grows both sides of that inclusion.  The
paper's own headline transformation goes the other way — journal §3.3, p.11,
says Write-Read Reordering is "valid under RA but not SC".  What *is* monotone,
and what this file is built on, is impossibility of a fixed outcome.
-/

universe u

namespace Isotope.Elgot.Opt

open Isotope.Elgot

/-! ## The assertion, in each model -/

/-- `assert ≠ c`, sequentially consistent version: diverge on `c`, otherwise
return.  `⊥` is the denotation of `iter (fun _ ↦ pure (Sum.inr ())) ()`
(`Brookes.iter_forever`). -/
def scAssertNe {Loc Val A : Type u} [DecidableEq A] (c : A) (a : A) :
    Brookes.SeqCst.Comp Loc Val A :=
  if a = c then ⊥ else Pure.pure a

/-- `assert ≠ c`, release/acquire version.  `⊥` is the denotation of
`iter (fun _ ↦ pure (Sum.inr ())) ()` (`RA.iter_diverge`). -/
def raAssertNe {Loc Val A : Type} [DecidableEq A] {R : RA.RuleSet} (c : A) (a : A) :
    RA.Comp R Loc Val A :=
  if a = c then ⊥ else Pure.pure a

/-! ## Sequential consistency: the transformation is sound -/

section SC

variable {Loc Val : Type u} [DecidableEq Loc] [DecidableEq Val]
  {x y : Loc} {v₀ v₁ : Val}

open Brookes Brookes.SeqCst

/-- The store-buffering program in the sequentially consistent model. -/
def scSB (x y : Loc) (v₁ : Val) : SeqCst.Comp Loc Val (Val × Val) :=
  Brookes.par (SeqCst.sb x y v₁) (SeqCst.sb y x v₁)

/-- **Deleting the assertion is sound under sequential consistency**, for
whole-program observations: every interference-free execution of `SB` from a
store in which `x` and `y` both hold `v₀` is an execution of
`SB ; assert⟨v₀,v₀⟩`.

The content is `SeqCst.sc_forbids_store_buffering`: the outcome `⟨v₀,v₀⟩` never
arises, so the assertion never fires and the post-processing is the identity on
every reachable value. -/
theorem sc_assert_elim_sound (hxy : x ≠ y) (hv : v₀ ≠ v₁)
    {μ σ : SeqCst.Store Loc Val} (hx : μ x = v₀) (hy : μ y = v₀)
    {t : SeqCst.Tr Loc Val} (hseq : SeqCst.Seq μ t σ) {r : Val × Val}
    (h : (t, r) ∈ scSB x y v₁) :
    (t, r) ∈ (scSB x y v₁ >>= scAssertNe (v₀, v₀)) := by
  have hne : r ≠ (v₀, v₀) := by
    rintro rfl
    exact SeqCst.sc_forbids_store_buffering hxy hv hx hy hseq h
  have hf : scAssertNe (Loc := Loc) (Val := Val) (v₀, v₀) r = Pure.pure r := if_neg hne
  have hb := Brookes.mem_bind (scSB x y v₁) (scAssertNe (v₀, v₀)) h
    (hf ▸ Brookes.mem_pure (c := SeqCst.rewriting (SeqCst.Store Loc Val)) r)
  simpa using hb

end SC

/-! ## Release/acquire: the transformation is unsound -/

section RA

open Isotope.Elgot.RA

variable {Loc Val : Type} [DecidableEq Loc] [DecidableEq Val] {R : RuleSet}

omit [DecidableEq Loc] [DecidableEq Val] in
/-- No trace of `P ; assert ≠ c` returns `c`: the assertion's branch at `c` is
the empty computation, and every rewrite preserves the returned value
(`Refines.ret_eq`). -/
theorem raAssert_ret_ne {A : Type} [DecidableEq A] (c : A) (P : Comp R Loc Val A)
    {π : PreTrace Loc Val A}
    (h : π ∈ (P >>= raAssertNe c : Comp R Loc Val A).traces) : π.ret ≠ c := by
  rw [Comp.traces_bind] at h
  obtain ⟨π₀, ⟨τ, υ, hs, hτ, hυ, -, rfl⟩, hr⟩ := h
  rw [← hr.ret_eq]
  change υ.ret ≠ c
  have hυ' : υ ∈ (raAssertNe (R := R) (Loc := Loc) (Val := Val) c τ.ret).traces := hυ
  by_cases hc : τ.ret = c
  · have hbot : (raAssertNe (R := R) (Loc := Loc) (Val := Val) c τ.ret) = ⊥ := if_pos hc
    rw [hbot] at hυ'
    exact absurd hυ' (by simp)
  · have hpure : (raAssertNe (R := R) (Loc := Loc) (Val := Val) c τ.ret)
        = Pure.pure τ.ret := if_neg hc
    rw [hpure] at hυ'
    rw [closure_pureGen_ret τ.ret hυ']
    exact hc

variable [Finite Loc] [Nonempty Loc] {x y : Loc} {v₀ v₁ : Val} {t₀ : ℚ}

/-- The store-buffering program in the release/acquire model, at rule set `R`. -/
def raSB (R : RuleSet) (x y : Loc) (v₁ : Val) : Comp R Loc Val (Val × Val) :=
  (store x v₁ >>= fun _ ↦ load y).par (store y v₁ >>= fun _ ↦ load x)

/-- **Deleting the assertion is unsound under release/acquire.**  The
single-transition trace of `Isotope/Elgot/RA/Opt/StoreBuffering.lean` — an
interference-free whole-program execution from the paper's initial memory — is
an execution of `SB` and is *not* an execution of `SB ; assert⟨v₀,v₀⟩`.

Valid at every rule set containing `Mumble`, hence at the `𝔠`-model, at the
Concrete model `C = 𝔤𝔠` and at the Abstract model `A = 𝔤𝔠𝔞`. -/
theorem ra_assert_elim_unsound (hMu : Rule.Mu ∈ R) (hxy : x ≠ y) :
    ∃ π : PreTrace Loc Val (Val × Val),
      π.ch = Chro.single ⟨sbMem0 v₀ t₀, sbMem2 v₀ v₁ t₀ x y⟩ ∧
      π.ivw = (fun _ ↦ t₀) ∧ π.ret = (v₀, v₀) ∧
      π ∈ (raSB R x y v₁).traces ∧
      π ∉ (raSB R x y v₁ >>= raAssertNe (v₀, v₀)).traces := by
  refine ⟨_, rfl, rfl, rfl,
    ra_admits_store_buffering (R := R) (v₀ := v₀) (v₁ := v₁) (t₀ := t₀) hMu hxy, ?_⟩
  intro hmem
  exact raAssert_ret_ne (v₀, v₀) (raSB R x y v₁) hmem rfl

end RA

/-! ## The separation -/

section Separation

open Isotope.Elgot.RA (Rule RuleSet)

variable {Loc Val : Type} [DecidableEq Loc] [DecidableEq Val] [Finite Loc] [Nonempty Loc]

/-- **Sequential consistency and release/acquire are separated by the
elimination of a store-buffering assertion.**

Half (i): under sequential consistency, `SB ; assert⟨v₀,v₀⟩ ↠ SB` is sound for
interference-free whole-program executions from an all-`v₀` store.

Half (ii): under release/acquire it is unsound, and the counterexample is itself
an interference-free whole-program execution — a single-transition trace out of
the paper's initial memory, the shape of the paper's own Soundness theorem
(journal Thm. 8.12, p.42).  Half (ii) holds at every rule set containing
`Mumble`, so at the Concrete model `C` and the Abstract model `A` alike.

The mechanism is exactly the difference between the two states: under sequential
consistency `read ℓ` returns `μ ℓ`, the unique current value, whereas under
release/acquire a thread reads whichever message its own view points at, and
each thread advanced its view only at its *own* location.

This is **not** the claim that sequential consistency validates more
transformations in general; see the module docstring. -/
theorem store_buffering_separates {R : RuleSet} (hMu : Rule.Mu ∈ R)
    (v₀ v₁ : Val) (t₀ : ℚ) (x y : Loc) (hxy : x ≠ y) (hv : v₀ ≠ v₁) :
    (∀ (μ σ : Brookes.SeqCst.Store Loc Val) (t : Brookes.SeqCst.Tr Loc Val)
        (r : Val × Val), μ x = v₀ → μ y = v₀ → Brookes.SeqCst.Seq μ t σ →
        (t, r) ∈ scSB x y v₁ →
          (t, r) ∈ (scSB x y v₁ >>= scAssertNe (v₀, v₀)))
    ∧ (∃ π : RA.PreTrace Loc Val (Val × Val),
        π.ch = RA.Chro.single ⟨RA.sbMem0 v₀ t₀, RA.sbMem2 v₀ v₁ t₀ x y⟩ ∧
        π.ivw = (fun _ ↦ t₀) ∧ π.ret = (v₀, v₀) ∧
        π ∈ (raSB R x y v₁).traces ∧
        π ∉ (raSB R x y v₁ >>= raAssertNe (v₀, v₀)).traces) :=
  ⟨fun _ _ _ _ hx hy hseq hmem ↦ sc_assert_elim_sound hxy hv hx hy hseq hmem,
   ra_assert_elim_unsound hMu hxy⟩

end Separation

end Isotope.Elgot.Opt
