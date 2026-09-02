import Isotope.Elgot.Brookes.SeqCst.Definability

/-!
# Full abstraction for the shared-variable parallel language

> **Proposition 7.1** (Brookes, *Full Abstraction for a Shared-Variable Parallel
> Language*, Inform. and Comput. 127(2):145–163, 1996, journal p. 151).
> *The transition traces semantics `T` is inequationally fully abstract: for all
> commands `C` and `C'`, `C ⊑_T C' ⟺ C ≤_M C'`.*

`fullAbstraction` below is that statement for the semantics of
`Isotope/Elgot/Brookes/SeqCst/Syntax.lean` and the contextual preorder of
`Isotope/Elgot/Brookes/SeqCst/Context.lean`, and `fullAbstraction_eq` is its
equational corollary `C ≡_T C' ⟺ C =_M C'`.

Both halves are proved:

* soundness (`den_le_ctxLe`, in `Context.lean`) is compositionality plus
  monotonicity of every construct;
* completeness (`ctxLe_den_le`) is Brookes's definability argument — for every
  transition trace there is a separating context — with the combinatorial step
  he leaves as "easy to see" discharged in `Chunk.lean`.

## Honest boundary

What is **not** formalized, and must not be read into the statement:

1. **No operational semantics.**  Brookes defines `T` and `M` operationally
   (journal §3, §4, §6) and *proves* the compositional clauses (Proposition 6.2)
   and `M[C] = {(s,s') | (s,s') ∈ T[C]}`.  Here the compositional clauses are
   the **definition** of `den`, and `obs` is defined as the one-pair fragment of
   `den`.  Proposition 6.2 — the bridge between the two — is not formalized.
   Everything below is therefore a theorem about the denotational `T` and the
   contextual preorder induced by the denotationally-defined observation.
2. **A restricted expression language.**  Constants and identifiers only, and
   boolean expressions are finite conjunctions of equations closed under
   negation.  This is the fragment Brookes's own gadgets `IS_s` need (journal
   p. 148); arbitrary arithmetic is orthogonal to the argument but is absent, so
   the theorem is stated for this language, not for his verbatim grammar.
3. **Total, finitely-indexed states.**  `Store Loc Val = Loc → Val` with `Loc` a
   `Fintype`.  Brookes uses finite partial maps and carries `dom(s)` side
   conditions; those disappear here.
4. **Only Proposition 4.3 for the record.**  Brookes also shows the contextual
   preorders induced by partial correctness and by *state traces* coincide.  The
   state-trace observation is not formalized.
5. **Finite traces, partial correctness.**  As in the paper's main development;
   his §9 fine-grained granularity and the fair infinite-trace extension are out
   of scope.
6. **`await` bodies are unrestricted.**  Brookes restricts them syntactically to
   sequences of assignments to make them atomic operationally.  Since there is
   no operational semantics here, the clause is taken verbatim for an arbitrary
   body; this makes the language *larger*, so both halves of full abstraction
   still concern the same set of contexts.

Point 1 is the substantive one.  Everything else narrows or widens the language
in a way that is stated where it happens.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {Loc Val : Type u} [Fintype Loc] [DecidableEq Loc] [DecidableEq Val]

/- `Fintype Loc` does not appear in the *statements* below, only in their proofs:
it is what makes `IS` and `MAKE`, hence the separating contexts, definable. -/
set_option linter.unusedFintypeInType false

/-- **The separating contexts suffice.**  If `C` and `C'` cannot be told apart by
any context of the shape `[−] ∥ DO u`, their trace sets are already ordered.

This is Brookes's definability argument.  The trace is nonempty because command
denotations are `ε`-free (`nil_not_mem_den`), so it is `zip s u s'` for some
interruptions `u` (`exists_zip`), and `obs_sep_iff` turns membership into an
observation. -/
theorem den_le_of_sep {C C' : Com Loc Val}
    (h : ∀ (v : Trace (Store Loc Val × Store Loc Val)) (s s' : Store Loc Val),
      Obs ((sep v).plug C) s s' → Obs ((sep v).plug C') s s') : den C ≤ den C' := by
  apply le_of_mem
  intro t a ht
  by_cases hnil : t = []
  · exact absurd (hnil ▸ ht) (nil_not_mem_den C a)
  · obtain ⟨s, v, s', rfl⟩ := exists_zip hnil
    exact (obs_sep_iff C' v s s').1 (h v s s' ((obs_sep_iff C v s s').2 ht))

/-- **Completeness (Brookes, Proposition 7.1, hard half): `C ≤_M C' ⇒ C ⊑_T C'`.**
Contextual refinement implies trace refinement. -/
theorem ctxLe_den_le {C C' : Com Loc Val} (h : CtxLe C C') : den C ≤ den C' :=
  den_le_of_sep fun v s s' ↦ h (sep v) s s'

/-- **Full abstraction (Brookes, Proposition 7.1).**  The transition traces
semantics is inequationally fully abstract: trace refinement coincides with
contextual refinement. -/
theorem fullAbstraction {C C' : Com Loc Val} : den C ≤ den C' ↔ CtxLe C C' :=
  ⟨den_le_ctxLe, ctxLe_den_le⟩

/-- **Equational full abstraction.**  Two commands have the same transition
traces iff they are interchangeable in every program context. -/
theorem fullAbstraction_eq {C C' : Com Loc Val} : den C = den C' ↔ CtxEq C C' := by
  constructor
  · intro h
    exact ⟨den_le_ctxLe h.le, den_le_ctxLe h.ge⟩
  · rintro ⟨h₁, h₂⟩
    exact le_antisymm (ctxLe_den_le h₁) (ctxLe_den_le h₂)

/-- The contextual preorder is already decided by the parallel contexts
`[−] ∥ DO u`: no other context shape is needed. -/
theorem ctxLe_iff_sep {C C' : Com Loc Val} :
    CtxLe C C' ↔ ∀ (v : Trace (Store Loc Val × Store Loc Val)) (s s' : Store Loc Val),
      Obs ((sep v).plug C) s s' → Obs ((sep v).plug C') s s' :=
  ⟨fun h v s s' ↦ h (sep v) s s', fun h ↦ den_le_ctxLe (den_le_of_sep h)⟩

end SeqCst

end Isotope.Elgot.Brookes
