import Isotope.Pomset.Quotient
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Hom.Set

/-!
# Linear pomsets, faithfulness, and non-linearity

The paper writes linearly ordered pomsets in list notation and reads a buffer
`Buf = 𝒜_b*` as such a pomset.  `PrePom.ofList` is that reading.

Two facts pin down exactly how much of the pomset structure is real:

* `ofList_deq_iff`: on the `δ`-free fragment, `ofList` is *injective* up to the quotient, so
  `Pom` restricted to that fragment is the free monoid on the alphabet.  Without this, the
  reading of emitted effects as pomsets would be an unjustified list encoding.
* `mk_seq_ne_mk_par`: the quotient nonetheless distinguishes `a;b` from `a ∥ b`, so `Pom` is
  strictly richer than the free monoid outside that fragment.

## Honest boundary

Both statements are about *finite* pomsets over an arbitrary alphabet.  Neither says
anything about concurrent behaviour: `mk_seq_ne_mk_par` is a statement about pomsets, not
about a parallel composition of morphisms, which is not formalised anywhere here.
-/

universe u

namespace Isotope.Pomset

namespace PrePom

variable {A : Type u}

/-- The **linear** pomset presentation of a list `[a₀, …, a_{n-1}]`, ordered by index.
This is how the paper reads a buffer as a pomset. -/
def ofList (l : List A) : PrePom A :=
  ⟨l.length, ⟨fun i => l[i.1], fun i j => i ≤ j, fun _ => le_refl _,
    fun h h' => le_trans h h', fun h h' => le_antisymm h h'⟩⟩

/-- The linear order on `Fin (m + n)` *is* the lexicographic sum of the two linear orders.
This is the one genuinely arithmetic lemma of the development. -/
theorem lex_finSumFinEquiv {m n : ℕ} (i j : Fin (m + n)) :
    Sum.Lex (· ≤ · : Fin m → Fin m → Prop) (· ≤ · : Fin n → Fin n → Prop)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j) ↔ i ≤ j := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [finSumFinEquiv_symm_apply_castAdd, Sum.lex_inl_inl, Fin.le_def, Fin.val_castAdd]
    | right j =>
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      refine iff_of_true (Sum.Lex.sep _ _) ?_
      simp only [Fin.le_def, Fin.val_castAdd, Fin.val_natAdd]; omega
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd]
      refine iff_of_false (fun h => by cases h) ?_
      simp only [Fin.le_def, Fin.val_castAdd, Fin.val_natAdd]; omega
    | right j =>
      simp only [finSumFinEquiv_symm_apply_natAdd, Sum.lex_inr_inr, Fin.le_def, Fin.val_natAdd]
      omega

/-- The label of a concatenated list, read through the `Fin` splitting. -/
theorem elim_getElem_finSumFinEquiv (l m : List A) (k : Fin (l.length + m.length))
    (i : Fin (l ++ m).length) (h : (i : ℕ) = (k : ℕ)) :
    Sum.elim (fun a : Fin l.length => l[a.1]) (fun b : Fin m.length => m[b.1])
        (finSumFinEquiv.symm k) = (l ++ m)[i.1] := by
  induction k using Fin.addCases with
  | left a =>
    simp only [finSumFinEquiv_symm_apply_castAdd, Sum.elim_inl]
    simp only [Fin.val_castAdd] at h
    rw [List.getElem_append_left (h ▸ a.2)]
    congr 1
    exact h.symm
  | right b =>
    simp only [finSumFinEquiv_symm_apply_natAdd, Sum.elim_inr]
    simp only [Fin.val_natAdd] at h
    rw [List.getElem_append_right (by omega)]
    congr 1
    omega

/-- Concatenation of lists is sequential composition of their linear pomsets. -/
def ofListAppendLIso (l m : List A) :
    LIso (ofList (l ++ m)).toLPoset ((ofList l).toLPoset.lseq (ofList m).toLPoset) where
  toEquiv := (finCongr (List.length_append ..)).trans finSumFinEquiv.symm
  label_eq i := elim_getElem_finSumFinEquiv l m _ i rfl
  le_iff i j :=
    (lex_finSumFinEquiv _ _).trans
      (by simp only [finCongr_apply]; exact Iff.rfl)

/-- Concatenation of lists is sequential composition, in the `δ`-quotient. -/
theorem ofList_append [Tick A] (l m : List A) :
    ofList (l ++ m) ≈ (ofList l).seq (ofList m) :=
  ⟨(DIso.ofLIso (ofListAppendLIso l m)).trans (DIso.ofLIso ((ofList l).seqLIso (ofList m)).symm)⟩

section Faithful

variable [Tick A]

/-- On a `δ`-free list every event is live. -/
def liveOfList {l : List A} (h : (tick : A) ∉ l) :
    Fin l.length ≃ (ofList l).toLPoset.Live tick where
  toFun i := ⟨i, fun hc => h (hc ▸ List.getElem_mem i.2)⟩
  invFun x := x.1
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Faithfulness of the linear embedding.**  On the `δ`-free fragment, `ofList` is
injective up to the `δ`-quotient: distinct `δ`-free lists present distinct pomsets.  This is
what licenses reading a buffer, or an emitted effect, as a genuine pomset rather than as an
arbitrary list encoding. -/
theorem ofList_deq_iff {l m : List A} (hl : (tick : A) ∉ l) (hm : (tick : A) ∉ m) :
    ofList l ≈ ofList m ↔ l = m := by
  constructor
  · rintro ⟨d⟩
    -- The `δ`-isomorphism is a full order isomorphism of the index sets.
    set f : Fin l.length ≃ Fin m.length :=
      (liveOfList hl).trans (d.toEquiv.trans (liveOfList hm).symm) with hf
    have hle : ∀ i j : Fin l.length, f i ≤ f j ↔ i ≤ j := fun i j =>
      d.le_iff (liveOfList hl i) (liveOfList hl j)
    have hlab : ∀ i : Fin l.length, m.get (f i) = l.get i := fun i =>
      d.label_eq (liveOfList hl i)
    have hlen : l.length = m.length := by
      simpa using Fintype.card_congr f
    -- Reindex to an order automorphism of `Fin l.length`, which must be the identity.
    let g : Fin l.length ≃o Fin l.length :=
      { toEquiv := f.trans (finCongr hlen).symm
        map_rel_iff' := by
          intro i j
          simp only [Equiv.trans_apply, finCongr_symm, finCongr_apply, Fin.le_def, Fin.val_cast]
          exact (Fin.le_def).symm.trans (hle i j) }
    have hg : g = OrderIso.refl _ := Subsingleton.elim _ _
    have hfin : ∀ i : Fin l.length, f i = Fin.cast hlen i := by
      intro i
      have h4 : g i = i := by rw [hg]; rfl
      apply Fin.ext
      have : ((f i : Fin m.length) : ℕ) = (i : ℕ) := congrArg Fin.val h4
      simpa using this
    refine List.ext_getElem hlen ?_
    intro i h₁ h₂
    have h3 := hlab ⟨i, h₁⟩
    rw [hfin ⟨i, h₁⟩] at h3
    exact h3.symm
  · rintro rfl
    exact Setoid.refl _

end Faithful

section NonLinear

variable [Tick A]

omit [Tick A] in
/-- In the parallel composition of two one-event pomsets, comparable events are equal. -/
theorem lpar_single_le_eq {a b : A} {x y : Fin (single a).card ⊕ Fin (single b).card}
    (h : ((single a).toLPoset.lpar (single b).toLPoset).le x y) : x = y := by
  rcases x with x | x <;> rcases y with y | y
  · exact congrArg Sum.inl
      (Fin.ext ((Nat.lt_one_iff.mp x.isLt).trans (Nat.lt_one_iff.mp y.isLt).symm))
  · cases h
  · cases h
  · exact congrArg Sum.inr
      (Fin.ext ((Nat.lt_one_iff.mp x.isLt).trans (Nat.lt_one_iff.mp y.isLt).symm))

/-- **The pomset quotient is not the free monoid.**  For distinct live actions `a` and `b`,
the ordered pomset `a;b` differs from the concurrent pomset `a ∥ b`.  Together with
`ofList_deq_iff` this says exactly how much the pomset layer buys: on the `δ`-free linear
fragment `Pom` *is* the free monoid, and strictly richer outside it. -/
theorem seq_not_equiv_par {a b : A} (ha : a ≠ tick) (hb : b ≠ tick) :
    ¬ ((single a).seq (single b) ≈ (single a).par (single b)) := by
  rintro ⟨d⟩
  set e : DIso tick ((single a).toLPoset.lseq (single b).toLPoset)
      ((single a).toLPoset.lpar (single b).toLPoset) :=
    (DIso.ofLIso ((single a).seqLIso (single b)).symm).trans
      (d.trans (DIso.ofLIso ((single a).parLIso (single b)))) with he
  let u : ((single a).toLPoset.lseq (single b).toLPoset).Live tick :=
    ⟨Sum.inl ⟨0, Nat.zero_lt_one⟩, ha⟩
  let v : ((single a).toLPoset.lseq (single b).toLPoset).Live tick :=
    ⟨Sum.inr ⟨0, Nat.zero_lt_one⟩, hb⟩
  have huv : u ≠ v := fun h => absurd (congrArg Subtype.val h) (by simp [u, v])
  have hlt : ((single a).toLPoset.lseq (single b).toLPoset).le u.1 v.1 := Sum.Lex.sep _ _
  have := lpar_single_le_eq ((e.le_iff u v).2 hlt)
  exact huv (e.toEquiv.injective (Subtype.ext this))

/-- The same, in the quotient. -/
theorem _root_.Isotope.Pomset.Pom.mk_seq_ne_mk_par {a b : A} (ha : a ≠ tick) (hb : b ≠ tick) :
    Pom.mk (single a) * Pom.mk (single b) ≠ Pom.par (Pom.mk (single a)) (Pom.mk (single b)) :=
  fun h => seq_not_equiv_par ha hb (Pom.mk_eq_mk.1 h)

end NonLinear

end PrePom

end Isotope.Pomset
