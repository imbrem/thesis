import Isotope.Elgot.RA.Opt.Basic
import Isotope.Elgot.RA.Opt.Sequential
import Isotope.Elgot.RA.Opt.StoreBuffering

/-!
# Program transformations in the release/acquire model

Soundness proofs, in the models of Dvir, Kammar and Lahav (`release-acquire`,
TOPLAS 47(2):7), for transformations from their Fig. 3 (journal p.12) and
Table 3 (journal p.44), together with the compositionality lemmas that make them
usable inside larger programs.

## Direction convention

`P ≤ Q` unfolds to `P.traces ⊆ Q.traces`, and validates the paper's `Q ↠ P`
(journal §3.3, p.11: the transformation `M ↠ N` is validated by `⟦N⟧ ⊑ ⟦M⟧`).
The *target* of a transformation has the *smaller* trace set.  The paper's own
prose for Proposition E.1 states this backwards; the erratum is already recorded
in `Isotope/Elgot/RA/Exchange.lean`.

## Contents

`Opt/Basic.lean`
: `Comp.le_of_gen_subset_closure`; `Comp.approx_mono` and `Comp.iterate_mono`;
  `mem_pure_of_own_empty`; `Comp.traces_bind_pure_comp`.

`Opt/StoreBuffering.lean`
: `ra_admits_store_buffering` — an explicit single-transition trace, from the
  paper's initial memory, in which `(x:=v₁ ; y?) ∥ (y:=v₁ ; x?)` returns
  `⟨v₀, v₀⟩`.  The denotational form of the paper's operational Example 5.3
  (journal p.19).  Valid at every rule set containing `Mumble`, hence at the
  Concrete model `C` and at the Abstract model `A` alike.

`Opt/Sequential.lean`
: Irrelevant Read Elimination (Prop. E.3) and Introduction (Prop. E.2), and the
  *equalities* `load_bind_pure_eq`, `load_bind_eq`, `load_bind_load_eq` that
  package them; Write-Read Elimination (`store_pure_le_store_load`, the
  `𝔞`-free row of Prop. E.9); Atomic Store (`xchg_le_store`, Prop. E.4); and
  the loop corollary `iterate_load_body`.

## Honest boundary

Read this before citing anything here.

1. **These are theorems about the model, not about a syntax.**  Each is a
   statement about `Comp R Loc Val` computations built from `store`, `rmw`,
   `load`, `>>=` and `∥∥∥`, universally quantified over locations, values and
   the rule set within a named range.  Nothing here is connected to the
   repository's `λ`-iter syntax or its denotation: `λ`-iter has **no** memory
   instructions (its instruction signature is an opaque parameter `Φ`), **no**
   parallel composition, and a **symmetric** equational judgment, whereas every
   transformation here is directed.  Do not describe any of it as "sound for
   `λ`-iter".
2. **Context closure is not adequacy.**  `Comp.bind_mono`, `Comp.par_mono` and
   `Comp.iterate_mono` make refinement a precongruence for every construct of
   the model, so a refinement may be applied under an arbitrary program context
   built from those constructs.  That is a *denotational* statement.  The
   paper's adequacy theorem (journal §8, Thm. 8.12 and the completeness
   direction), which is what licences reading a refinement as "no observable
   behaviour is added", is **not** formalized here; the operational semantics
   is not formalized at all.
3. **What is proved is exactly the listed rows.**  Table 3 also contains
   Generalized Sequencing (E.1, in `Exchange.lean`), Sequencing and Symmetry
   (asserted without proof in the paper; proved in `Exchange.lean` and
   `Parallel.lean` as original work), Write-Read Deorder (E.5), RMW Expansion
   (E.6), RMW-RMW Elimination (E.8), the general Write-RMW Elimination (E.9),
   RMW-Write Elimination (E.11) and Write-Write Elimination (E.10).  Of these,
   only Write-Write Elimination is treated here, in `Isotope/Elgot/Opt/`, and
   there only as an *unsoundness* result for the concrete model.  The rest are
   not attempted.  In particular Write-Read Deorder (E.5) is blocked on a
   documented boundary: `IsInfMem` is a hypothesis of `parGen`, never a
   conclusion, so the paper's `inf_μ{κ,σ}` cannot yet be *constructed* for a
   general interleaving.
4. **Rule-set discipline.**  `LawfulMonad` is available only at `𝔠` and at the
   Concrete model `𝔤𝔠`.  Both unit laws — and `Comp.traces_bind_pure_comp`,
   which the transformations here run on — hold on the whole range
   `𝔠 ⊆ R ⊆ 𝔤𝔠 ∪ {Ti, Ab}`.  At the Abstract model `𝔤𝔠𝔞` the unit laws
   **fail** (`Abstract.dilute_return`), so none of the results here is stated
   there, and statements needing `Dilute` would have to be made `bind`-free.
-/
