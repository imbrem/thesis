import Isotope.Elgot.Opt.StoreBuffering
import Isotope.Elgot.Opt.WriteWrite

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

`Opt/WriteWrite.lean`
: the two most elementary store optimizations, side by side.  Write-Read
  Elimination `ℓ:=v ; ℓ? ↠ ℓ:=v ; v` transfers from sequential consistency to
  the release/acquire *Concrete* model verbatim
  (`write_read_elim_transfers`); Write-Write Elimination
  `ℓ:=v ; ℓ:=w ↠ ℓ:=w` does not — it is sound under sequential consistency by a
  single mumble and **unsound** in the release/acquire `𝔠`-model
  (`write_write_elim_fails_in_cRules`), because a release/acquire memory keeps
  the superseded write as a message and no `𝔠`-rule can delete it.  Table 3's
  own labelling predicts the split: the Write-Read row carries no abstract-rule
  label, Write-Write carries `Ab`.

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
5. **`Opt/WriteWrite.lean` is a different kind of statement, and is labelled as
   such.**  Write-Write Elimination is listed in the paper's Table 3
   (journal p.44) as `ℓ:=w ; ℓ:=v ↠^Ab ℓ:=v`: the **Abstract** model `A`
   validates it, using the abstract rule `Absorb`.  So
   `write_write_elim_fails_in_cRules` separates a *level of the release/acquire
   tower* from sequential consistency, not release/acquire from sequential
   consistency, and it must never be stated without that caveat.  Two further
   limits: the unsoundness is proved for `R ⊆ 𝔠` and **not** for the Concrete
   model `C = 𝔤𝔠` (the argument runs on `Refines.c_sub`, which fails for `Ls`,
   `Ex` and `Cn`); and Prop. E.10, the soundness at `A`, is **not** proved
   here — the repository has the required `Absorb` rewrite only at one concrete
   instance, `RA.Abstract.absorb_two_writes`.
6. **Parallel composition is outside the monad** in both models, and this
   repository's `λ`-iter syntax has no parallel composition at all.  The
   separation is therefore a statement about the two *models*, not about the
   `λ`-iter denotational semantics.
-/
