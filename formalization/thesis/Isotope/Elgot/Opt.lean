import Isotope.Elgot.Opt.StoreBuffering

/-!
# Transformations compared across memory models

Results that span two of this repository's memory models and therefore belong to
neither.  Model-internal transformation soundness for release/acquire lives in
`Isotope/Elgot/RA/Opt.lean`.

## Contents

`Opt/StoreBuffering.lean`
: the **store-buffering separation** between the Brookes model of sequential
  consistency and Dvir, Kammar and Lahav's release/acquire models
  (`release-acquire`, TOPLAS 47(2):7).  Both halves are proved:
  `sc_assert_elim_sound` (the transformation "delete the assertion
  `¬(a = v₀ ∧ b = v₀)`" is sound under sequential consistency, for
  interference-free whole-program executions) and `ra_assert_elim_unsound`
  (it is unsound under release/acquire, by an explicit trace that is in one
  denotation and provably not in the other).  `store_buffering_separates`
  conjoins them.

## Honest boundary

Read this before citing anything here.

1. **The observable, and the side condition.**  Both halves are about
   *whole-program, interference-free* executions.  On the sequentially
   consistent side that is the hypothesis `Seq μ t σ`; it **cannot be
   dropped**, because in the open compositional order the sequentially
   consistent model also admits `⟨v₀,v₀⟩` — the environment may restore `x`.
   On the release/acquire side the witness's chronicle is a *single
   transition* out of the paper's initial memory, which is the shape the
   paper's own Soundness theorem (journal Thm. 8.12, p.42) assigns to a
   whole-program evaluation.  So the counterexample lies inside the restricted
   class and the restriction is not doing the separating work.
2. **This is not "sequential consistency validates more transformations".**
   Soundness of `S ↠ T` is `⟦T⟧ ⊆ ⟦S⟧`; weakening a model grows both sides of
   that inclusion, so nothing is monotone in the model.  The paper's own
   headline transformation goes the other way (journal §3.3, p.11: Write-Read
   Reordering is "valid under RA but not SC").  What *is* monotone is
   impossibility of a fixed outcome, and that is what these theorems are built
   on.
3. **Denotational only.**  "Release/acquire admits store buffering" as an
   *operational* fact needs the adequacy theorem, which is not formalized here,
   and the paper's operational semantics is not formalized at all.  What is
   proved is the denotational statement, which matches the paper's own
   Example 5.3 (journal p.19).
4. **No model morphism.**  The two models' states are incomparable — a store
   `Loc → Val` against a set of timestamped messages plus a view — and no
   translation between them is defined or claimed.  What the two halves share
   is the source program (up to each model's own denotation brackets), the
   class of observations, and the observed value.
5. **A related but different separation, not claimed here.**  Write-Write
   Elimination `ℓ:=v ; ℓ:=w ↠ ℓ:=w` is sound under sequential consistency
   (`Brookes.SeqCst.write_le_write_write`) and is listed in the paper's Table 3
   (journal p.44) as `ℓ:=w ; ℓ:=v ↠^Ab ℓ:=v` — that is, the **Abstract** model
   validates it, using the abstract rule `Absorb`.  Anyone stating it as a
   separation must say that it separates the *Concrete* model from the
   *Abstract* one, not sequential consistency from release/acquire.  It is not
   proved in either direction here.
6. **Parallel composition is outside the monad** in both models, and this
   repository's `λ`-iter syntax has no parallel composition at all.  The
   separation is therefore a statement about the two *models*, not about the
   `λ`-iter denotational semantics.
-/
