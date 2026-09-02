import Isotope.Elgot.Brookes.SeqCst.Syntax

/-!
# Program contexts, the contextual preorder, and soundness

Brookes's substitutive preorder (journal p. 148, Definition following 4.2):

```
C ≤_M C'  ⟺  ∀ P[−]. P[C] ⊑_M P[C'],
```

where `P[−]` ranges over program contexts and `⊑_M` is inclusion of partial
correctness behaviours.  Our states are total, so his `dom(s)` side condition
disappears.

`Ctx` is the one-hole command context, spelled out constructor by constructor;
`plug P C` is his `P[C]`.

The soundness half of full abstraction (Brookes, Proposition 7.1, the direction
`C ⊑_T C' ⇒ C ≤_M C'`) is `den_le_ctxLe` below.  His proof is one paragraph:
*"Since `T` is a denotational semantics, for each program context `P[−]` the only
relevant aspect of `C` in determining `T[P[C]]` is `T[C]`.  Moreover, all
operations used in the semantic definitions are monotone with respect to set
inclusion."*  Formalizing it is exactly an induction over `Ctx` using one
monotonicity lemma per construct, which is what this file does.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {Loc Val : Type u}

/-! ## Monotonicity of the semantic operations -/

/-- Parallel composition of commands is monotone. -/
theorem par_den_mono {x x' y y' : Comp Loc Val PUnit} (hx : x ≤ x') (hy : y ≤ y') :
    ((fun _ ↦ PUnit.unit) <$> Brookes.par x y) ≤
      ((fun _ ↦ PUnit.unit) <$> Brookes.par x' y') := by
  apply le_of_mem
  intro t a hm
  obtain ⟨p, hp, hmem⟩ := mem_map_iff.1 hm
  exact mem_map_iff.2 ⟨p, hp, par_mono hx hy hmem⟩

/-- The conditional-critical-region construct is monotone. -/
theorem await_den_mono {p : Store Loc Val → Bool} {x y : Comp Loc Val PUnit} (h : x ≤ y) :
    atom (fun μ ν ↦ p μ = true ∧ obs x μ ν) ≤ atom (fun μ ν ↦ p μ = true ∧ obs y μ ν) :=
  atom_mono fun _ _ hR ↦ ⟨hR.1, obs_mono h hR.2⟩

/-! ## Contexts -/

/-- A one-hole command context: Brookes's `P[−]`. -/
inductive Ctx (Loc Val : Type u) : Type u
  | /-- The hole. -/ hole
  | /-- `P; C`. -/ seqL (P : Ctx Loc Val) (C : Com Loc Val)
  | /-- `C; P`. -/ seqR (C : Com Loc Val) (P : Ctx Loc Val)
  | /-- `P ∥ C`. -/ parL (P : Ctx Loc Val) (C : Com Loc Val)
  | /-- `C ∥ P`. -/ parR (C : Com Loc Val) (P : Ctx Loc Val)
  | /-- `if B then P else C`. -/ iteL (b : BExp Loc Val) (P : Ctx Loc Val) (C : Com Loc Val)
  | /-- `if B then C else P`. -/ iteR (b : BExp Loc Val) (C : Com Loc Val) (P : Ctx Loc Val)
  | /-- `while B do P`. -/ wh (b : BExp Loc Val) (P : Ctx Loc Val)
  | /-- `await B then P`. -/ await (b : BExp Loc Val) (P : Ctx Loc Val)

/-- `plug P C` is Brookes's `P[C]`. -/
def Ctx.plug : Ctx Loc Val → Com Loc Val → Com Loc Val
  | .hole, C => C
  | .seqL P C₂, C => .seq (P.plug C) C₂
  | .seqR C₁ P, C => .seq C₁ (P.plug C)
  | .parL P C₂, C => .par (P.plug C) C₂
  | .parR C₁ P, C => .par C₁ (P.plug C)
  | .iteL b P C₂, C => .ite b (P.plug C) C₂
  | .iteR b C₁ P, C => .ite b C₁ (P.plug C)
  | .wh b P, C => .wh b (P.plug C)
  | .await b P, C => .await b (P.plug C)

/-! ## Compositionality and monotonicity -/

/-- **Compositionality + monotonicity.**  Trace inclusion is preserved by every
program context.  This is the whole content of Brookes's soundness paragraph
(journal p. 151). -/
theorem den_plug_mono [DecidableEq Loc] [DecidableEq Val] {C C' : Com Loc Val}
    (h : den C ≤ den C') (P : Ctx Loc Val) : den (P.plug C) ≤ den (P.plug C') := by
  induction P with
  | hole => exact h
  | seqL P C₂ ih => exact bind_mono ih fun _ ↦ le_rfl
  | seqR C₁ P ih => exact bind_mono le_rfl fun _ ↦ ih
  | parL P C₂ ih => exact par_den_mono ih le_rfl
  | parR C₁ P ih => exact par_den_mono le_rfl ih
  | iteL b P C₂ ih => exact union2_mono (bind_mono le_rfl fun _ ↦ ih) le_rfl
  | iteR b C₁ P ih => exact union2_mono le_rfl (bind_mono le_rfl fun _ ↦ ih)
  | wh b P ih => exact bind_mono (star_mono (bind_mono le_rfl fun _ ↦ ih)) fun _ ↦ le_rfl
  | await b P ih => exact await_den_mono ih

/-! ## The contextual preorder -/

/-- **Brookes's substitutive preorder** `C ≤_M C'`: `C` may be replaced by `C'`
in every program context without adding partial-correctness behaviour. -/
def CtxLe [DecidableEq Loc] [DecidableEq Val] (C C' : Com Loc Val) : Prop :=
  ∀ P : Ctx Loc Val, ∀ μ ν : Store Loc Val, Obs (P.plug C) μ ν → Obs (P.plug C') μ ν

/-- **Brookes's substitutive equivalence** `C =_M C'`. -/
def CtxEq [DecidableEq Loc] [DecidableEq Val] (C C' : Com Loc Val) : Prop :=
  CtxLe C C' ∧ CtxLe C' C

theorem CtxLe.refl [DecidableEq Loc] [DecidableEq Val] (C : Com Loc Val) : CtxLe C C :=
  fun _ _ _ h ↦ h

theorem CtxLe.trans [DecidableEq Loc] [DecidableEq Val] {C C' C'' : Com Loc Val}
    (h : CtxLe C C') (h' : CtxLe C' C'') : CtxLe C C'' :=
  fun P μ ν hm ↦ h' P μ ν (h P μ ν hm)

/-- Taking the hole context shows the contextual preorder refines the plain
partial-correctness preorder. -/
theorem CtxLe.obs [DecidableEq Loc] [DecidableEq Val] {C C' : Com Loc Val} (h : CtxLe C C')
    {μ ν : Store Loc Val} (hm : Obs C μ ν) : Obs C' μ ν := h .hole μ ν hm

/-- **Soundness (Brookes, Proposition 7.1, easy half): `C ⊑_T C' ⇒ C ≤_M C'`.**
Trace refinement implies contextual refinement. -/
theorem den_le_ctxLe [DecidableEq Loc] [DecidableEq Val] {C C' : Com Loc Val}
    (h : den C ≤ den C') : CtxLe C C' :=
  fun P _ _ hm ↦ obs_mono (den_plug_mono h P) hm

end SeqCst

end Isotope.Elgot.Brookes
