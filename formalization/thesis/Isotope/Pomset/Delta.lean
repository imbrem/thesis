import Isotope.Pomset.PrePom

/-!
# The δ-quotient

The paper quotients pomsets "over the removal of arbitrarily many copies of `δ`".  Rather
than construct that erasure, we *define* the quotient relation to be an isomorphism of the
**live** subcarriers — the events not labelled `δ`.  This is `DIso`, and it makes the
congruence and unit laws for `;` and `∥` immediate from the corresponding facts about `Sum`.

Erasure is deliberately never constructed.  Note that erasure is *not* a homomorphism for
`;` in the general (infinite) setting: with `δ^ω` an infinite tick pomset,
`erase(δ^ω ; [x])` has empty live part after `trim`, whereas `erase(δ^ω) ; erase([x]) = [x]`.
This is exactly why the paper's definition carries a cardinality side condition.  Working
with `DIso` on the live subcarrier sidesteps the issue; in the finite fragment formalised
here the side condition is vacuous anyway.

## Honest boundary

`DIso` is the finite specialisation of the paper's quotient.  Nothing here handles infinite
carriers, `trim`, or the stream action.
-/

universe u v w x

namespace Isotope.Pomset

namespace LPoset

variable {A : Type u} {ι : Type v} {κ : Type w}

/-- The **live** subcarrier: the events not labelled by the null action `δ`. -/
abbrev Live (L : LPoset A ι) (δ : A) : Type v := {i : ι // L.label i ≠ δ}

end LPoset

/-- A `δ`-isomorphism: an isomorphism of the *live* sub-labelled-posets.  This is the
paper's quotient "over the removal of arbitrarily many copies of `δ`", stated without ever
constructing the erasure. -/
structure DIso {A : Type u} {ι : Type v} {κ : Type w} (δ : A)
    (L : LPoset A ι) (M : LPoset A κ) where
  /-- The underlying bijection of live subcarriers. -/
  toEquiv : L.Live δ ≃ M.Live δ
  /-- The bijection preserves labels. -/
  label_eq : ∀ i, M.label (toEquiv i) = L.label i
  /-- The bijection reflects and preserves the order. -/
  le_iff : ∀ i j, M.le (toEquiv i) (toEquiv j) ↔ L.le i j

namespace DIso

variable {A : Type u} {ι : Type v} {κ : Type w} {μ : Type x} {δ : A}
variable {L : LPoset A ι} {M : LPoset A κ} {N : LPoset A μ}

/-- Every isomorphism is a `δ`-isomorphism. -/
def ofLIso (f : LIso L M) : DIso δ L M where
  toEquiv := Equiv.subtypeEquiv f.toEquiv (fun i => by rw [f.label_eq])
  label_eq i := f.label_eq i
  le_iff i j := f.le_iff i j

/-- The identity `δ`-isomorphism. -/
def refl (δ : A) (L : LPoset A ι) : DIso δ L L := ofLIso (LIso.refl L)

/-- The inverse `δ`-isomorphism. -/
def symm (f : DIso δ L M) : DIso δ M L where
  toEquiv := f.toEquiv.symm
  label_eq j := by simpa using (f.label_eq (f.toEquiv.symm j)).symm
  le_iff i j := by simpa using (f.le_iff (f.toEquiv.symm i) (f.toEquiv.symm j)).symm

/-- Composition of `δ`-isomorphisms. -/
def trans (f : DIso δ L M) (g : DIso δ M N) : DIso δ L N where
  toEquiv := f.toEquiv.trans g.toEquiv
  label_eq i := by simpa using (g.label_eq (f.toEquiv i)).trans (f.label_eq i)
  le_iff i j := by simpa using (g.le_iff (f.toEquiv i) (f.toEquiv j)).trans (f.le_iff i j)

end DIso

namespace LPoset

variable {A : Type u} {ι : Type v} {κ : Type w}

/-- The live subcarrier of a lexicographic sum is the sum of the live subcarriers.
Written by hand, rather than via `Equiv.subtypeSum`, so that both directions reduce on
constructors: with the library equivalence the inverse is a `match` that `simp` will not
push through, and the case analyses in `DIso.lseq` stall. -/
def sumLive (δ : A) (L : LPoset A ι) (M : LPoset A κ) :
    L.Live δ ⊕ M.Live δ ≃ (L.lseq M).Live δ where
  toFun := Sum.elim (fun i => ⟨Sum.inl i.1, i.2⟩) (fun j => ⟨Sum.inr j.1, j.2⟩)
  invFun x := match x with
    | ⟨Sum.inl a, h⟩ => Sum.inl ⟨a, h⟩
    | ⟨Sum.inr b, h⟩ => Sum.inr ⟨b, h⟩
  left_inv := by rintro (i | i) <;> rfl
  right_inv := by rintro ⟨(a | b), h⟩ <;> rfl

/-- The same splitting for the disjoint (parallel) sum. -/
def sumLivePar (δ : A) (L : LPoset A ι) (M : LPoset A κ) :
    L.Live δ ⊕ M.Live δ ≃ (L.lpar M).Live δ where
  toFun := Sum.elim (fun i => ⟨Sum.inl i.1, i.2⟩) (fun j => ⟨Sum.inr j.1, j.2⟩)
  invFun x := match x with
    | ⟨Sum.inl a, h⟩ => Sum.inl ⟨a, h⟩
    | ⟨Sum.inr b, h⟩ => Sum.inr ⟨b, h⟩
  left_inv := by rintro (i | i) <;> rfl
  right_inv := by rintro ⟨(a | b), h⟩ <;> rfl

end LPoset

namespace DIso

variable {A : Type u} {ι : Type v} {κ : Type w} {μ : Type x} {δ : A}

/-- Sequential composition is a congruence for `δ`-isomorphism. -/
def lseq {ι' : Type v} {κ' : Type w}
    {L : LPoset A ι} {L' : LPoset A ι'} {M : LPoset A κ} {M' : LPoset A κ'}
    (f : DIso δ L L') (g : DIso δ M M') : DIso δ (L.lseq M) (L'.lseq M') where
  toEquiv :=
    ((LPoset.sumLive δ L M).symm.trans (Equiv.sumCongr f.toEquiv g.toEquiv)).trans
      (LPoset.sumLive δ L' M')
  label_eq := by
    rintro ⟨(i | i), h⟩
    exacts [f.label_eq ⟨i, h⟩, g.label_eq ⟨i, h⟩]
  le_iff := by
    rintro ⟨(i | i), hi⟩ ⟨(j | j), hj⟩
    · exact Sum.lex_inl_inl.trans ((f.le_iff ⟨i, hi⟩ ⟨j, hj⟩).trans Sum.lex_inl_inl.symm)
    · exact iff_of_true (Sum.Lex.sep _ _) (Sum.Lex.sep _ _)
    · exact iff_of_false (fun h => by cases h) (fun h => by cases h)
    · exact Sum.lex_inr_inr.trans ((g.le_iff ⟨i, hi⟩ ⟨j, hj⟩).trans Sum.lex_inr_inr.symm)

/-- Parallel composition is a congruence for `δ`-isomorphism. -/
def lpar {ι' : Type v} {κ' : Type w}
    {L : LPoset A ι} {L' : LPoset A ι'} {M : LPoset A κ} {M' : LPoset A κ'}
    (f : DIso δ L L') (g : DIso δ M M') : DIso δ (L.lpar M) (L'.lpar M') where
  toEquiv :=
    ((LPoset.sumLivePar δ L M).symm.trans (Equiv.sumCongr f.toEquiv g.toEquiv)).trans
      (LPoset.sumLivePar δ L' M')
  label_eq := by
    rintro ⟨(i | i), h⟩
    exacts [f.label_eq ⟨i, h⟩, g.label_eq ⟨i, h⟩]
  le_iff := by
    rintro ⟨(i | i), hi⟩ ⟨(j | j), hj⟩
    · exact Sum.liftRel_inl_inl.trans
        ((f.le_iff ⟨i, hi⟩ ⟨j, hj⟩).trans Sum.liftRel_inl_inl.symm)
    · exact iff_of_false (fun h => by cases h) (fun h => by cases h)
    · exact iff_of_false (fun h => by cases h) (fun h => by cases h)
    · exact Sum.liftRel_inr_inr.trans
        ((g.le_iff ⟨i, hi⟩ ⟨j, hj⟩).trans Sum.liftRel_inr_inr.symm)

/-- If every event of `M` is a `δ`, then `M` is a right unit for `;`. -/
def lseqUnitRight {L : LPoset A ι} {M : LPoset A κ} [IsEmpty (M.Live δ)] :
    DIso δ (L.lseq M) L where
  toEquiv := (LPoset.sumLive δ L M).symm.trans (Equiv.sumEmpty _ _)
  label_eq := by
    rintro ⟨(i | i), h⟩
    · rfl
    · exact (IsEmpty.false (⟨i, h⟩ : M.Live δ)).elim
  le_iff := by
    rintro ⟨(i | i), hi⟩ ⟨(j | j), hj⟩
    · exact Iff.symm Sum.lex_inl_inl
    · exact (IsEmpty.false (⟨j, hj⟩ : M.Live δ)).elim
    · exact (IsEmpty.false (⟨i, hi⟩ : M.Live δ)).elim
    · exact (IsEmpty.false (⟨i, hi⟩ : M.Live δ)).elim

/-- If every event of `L` is a `δ`, then `L` is a left unit for `;`. -/
def lseqUnitLeft {L : LPoset A ι} {M : LPoset A κ} [IsEmpty (L.Live δ)] :
    DIso δ (L.lseq M) M where
  toEquiv := (LPoset.sumLive δ L M).symm.trans (Equiv.emptySum _ _)
  label_eq := by
    rintro ⟨(i | i), h⟩
    · exact (IsEmpty.false (⟨i, h⟩ : L.Live δ)).elim
    · rfl
  le_iff := by
    rintro ⟨(i | i), hi⟩ ⟨(j | j), hj⟩
    · exact (IsEmpty.false (⟨i, hi⟩ : L.Live δ)).elim
    · exact (IsEmpty.false (⟨i, hi⟩ : L.Live δ)).elim
    · exact (IsEmpty.false (⟨j, hj⟩ : L.Live δ)).elim
    · exact Iff.symm Sum.lex_inr_inr

/-- If every event of `M` is a `δ`, then `M` is a right unit for `∥`. -/
def lparUnitRight {L : LPoset A ι} {M : LPoset A κ} [IsEmpty (M.Live δ)] :
    DIso δ (L.lpar M) L where
  toEquiv := (LPoset.sumLivePar δ L M).symm.trans (Equiv.sumEmpty _ _)
  label_eq := by
    rintro ⟨(i | i), h⟩
    · rfl
    · exact (IsEmpty.false (⟨i, h⟩ : M.Live δ)).elim
  le_iff := by
    rintro ⟨(i | i), hi⟩ ⟨(j | j), hj⟩
    · exact Iff.symm Sum.liftRel_inl_inl
    · exact (IsEmpty.false (⟨j, hj⟩ : M.Live δ)).elim
    · exact (IsEmpty.false (⟨i, hi⟩ : M.Live δ)).elim
    · exact (IsEmpty.false (⟨i, hi⟩ : M.Live δ)).elim

/-- Any two all-`δ` labelled posets are `δ`-isomorphic. -/
def ofIsEmpty {L : LPoset A ι} {M : LPoset A κ}
    [IsEmpty (L.Live δ)] [IsEmpty (M.Live δ)] : DIso δ L M where
  toEquiv := Equiv.equivOfIsEmpty _ _
  label_eq i := (IsEmpty.false i).elim
  le_iff i _ := (IsEmpty.false i).elim

end DIso

/-- An action alphabet with a distinguished null action `δ` ("tick"). -/
class Tick (A : Type u) where
  /-- The null action `δ`. -/
  tick : A

export Tick (tick)

namespace PrePom

variable {A : Type u} [Tick A]

/-- Two presentations are equivalent when their live subcarriers are isomorphic. -/
instance instSetoid : Setoid (PrePom A) where
  r p q := Nonempty (DIso tick p.toLPoset q.toLPoset)
  iseqv := ⟨fun _ => ⟨DIso.refl _ _⟩, fun ⟨f⟩ => ⟨f.symm⟩, fun ⟨f⟩ ⟨g⟩ => ⟨f.trans g⟩⟩

theorem equiv_def {p q : PrePom A} : p ≈ q ↔ Nonempty (DIso tick p.toLPoset q.toLPoset) :=
  Iff.rfl

instance : IsEmpty ((empty A).toLPoset.Live tick) := ⟨fun x => x.1.elim0⟩

instance : IsEmpty ((single (tick : A)).toLPoset.Live tick) := ⟨fun x => x.2 rfl⟩

/-- Sequential composition respects the `δ`-quotient. -/
theorem seq_congr {p p' q q' : PrePom A} (hp : p ≈ p') (hq : q ≈ q') :
    p.seq q ≈ p'.seq q' := by
  obtain ⟨f⟩ := hp; obtain ⟨g⟩ := hq
  exact ⟨((DIso.ofLIso (p.seqLIso q)).trans (DIso.lseq f g)).trans
    (DIso.ofLIso (p'.seqLIso q').symm)⟩

/-- Parallel composition respects the `δ`-quotient. -/
theorem par_congr {p p' q q' : PrePom A} (hp : p ≈ p') (hq : q ≈ q') :
    p.par q ≈ p'.par q' := by
  obtain ⟨f⟩ := hp; obtain ⟨g⟩ := hq
  exact ⟨((DIso.ofLIso (p.parLIso q)).trans (DIso.lpar f g)).trans
    (DIso.ofLIso (p'.parLIso q').symm)⟩

/-- Sequential composition is associative up to the `δ`-quotient. -/
theorem seq_assoc (p q r : PrePom A) : (p.seq q).seq r ≈ p.seq (q.seq r) :=
  ⟨(((DIso.ofLIso ((p.seq q).seqLIso r)).trans
      (DIso.lseq (DIso.ofLIso (p.seqLIso q)) (DIso.refl _ _))).trans
        ((DIso.ofLIso (LIso.lseqAssoc p.toLPoset q.toLPoset r.toLPoset)).trans
          (DIso.lseq (DIso.refl _ _) (DIso.ofLIso (q.seqLIso r).symm)))).trans
    (DIso.ofLIso (p.seqLIso (q.seq r)).symm)⟩

/-- Parallel composition is associative up to the `δ`-quotient. -/
theorem par_assoc (p q r : PrePom A) : (p.par q).par r ≈ p.par (q.par r) :=
  ⟨(((DIso.ofLIso ((p.par q).parLIso r)).trans
      (DIso.lpar (DIso.ofLIso (p.parLIso q)) (DIso.refl _ _))).trans
        ((DIso.ofLIso (LIso.lparAssoc p.toLPoset q.toLPoset r.toLPoset)).trans
          (DIso.lpar (DIso.refl _ _) (DIso.ofLIso (q.parLIso r).symm)))).trans
    (DIso.ofLIso (p.parLIso (q.par r)).symm)⟩

/-- Parallel composition is commutative up to the `δ`-quotient. -/
theorem par_comm (p q : PrePom A) : p.par q ≈ q.par p :=
  ⟨((DIso.ofLIso (p.parLIso q)).trans
    (DIso.ofLIso (LIso.lparComm p.toLPoset q.toLPoset))).trans
      (DIso.ofLIso (q.parLIso p).symm)⟩

/-- Any all-`δ` presentation is a right unit for `;`. -/
theorem seq_unit_right {u : PrePom A} [IsEmpty (u.toLPoset.Live tick)] (p : PrePom A) :
    p.seq u ≈ p :=
  ⟨(DIso.ofLIso (p.seqLIso u)).trans DIso.lseqUnitRight⟩

/-- Any all-`δ` presentation is a left unit for `;`. -/
theorem seq_unit_left {u : PrePom A} [IsEmpty (u.toLPoset.Live tick)] (p : PrePom A) :
    u.seq p ≈ p :=
  ⟨(DIso.ofLIso (u.seqLIso p)).trans DIso.lseqUnitLeft⟩

/-- Any all-`δ` presentation is a right unit for `∥`. -/
theorem par_unit_right {u : PrePom A} [IsEmpty (u.toLPoset.Live tick)] (p : PrePom A) :
    p.par u ≈ p :=
  ⟨(DIso.ofLIso (p.parLIso u)).trans DIso.lparUnitRight⟩

/-- The paper's unit `{δ}` and the empty presentation agree in the quotient. -/
theorem single_tick_equiv_empty : single (tick : A) ≈ empty A := ⟨DIso.ofIsEmpty⟩

end PrePom

end Isotope.Pomset
