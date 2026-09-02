import Mathlib.Logic.Equiv.Sum
import Mathlib.Data.Sum.Order

/-!
# Labelled posets

The raw material of pomsets: a partial order on an explicit carrier `ι` together with a
labelling `ι → A`, and the notion of label- and order-preserving isomorphism.

The order is a *field*, not a `PartialOrder` instance, so that a carrier may be reindexed
along an arbitrary `Equiv` without transporting instances.

## Honest boundary

Nothing here is specific to finiteness or to the null action `δ`; those enter in
`Isotope.Pomset.PrePom` and `Isotope.Pomset.Delta` respectively.
-/

universe u v w x

namespace Isotope.Pomset

/-- A labelled poset: a partial order on `ι` together with an `A`-labelling.
The order is kept as plain fields rather than as a `PartialOrder` instance so that the
carrier may be reindexed freely. -/
structure LPoset (A : Type u) (ι : Type v) where
  /-- The labelling of events by actions. -/
  label : ι → A
  /-- The causal order on events. -/
  le : ι → ι → Prop
  /-- Reflexivity of `le`. -/
  le_refl : ∀ i, le i i
  /-- Transitivity of `le`. -/
  le_trans : ∀ {i j k}, le i j → le j k → le i k
  /-- Antisymmetry of `le`. -/
  le_antisymm : ∀ {i j}, le i j → le j i → i = j

namespace LPoset

variable {A : Type u} {ι : Type v} {κ : Type w} {μ : Type x}

/-- Reindex a labelled poset along an equivalence of carriers. -/
def comap (L : LPoset A ι) (e : κ ≃ ι) : LPoset A κ where
  label k := L.label (e k)
  le k k' := L.le (e k) (e k')
  le_refl _ := L.le_refl _
  le_trans h h' := L.le_trans h h'
  le_antisymm h h' := e.injective (L.le_antisymm h h')

/-- Lexicographic (sequential) sum: everything in `L` precedes everything in `M`.
This is the paper's `α;β` before the carrier is reindexed. -/
def lseq (L : LPoset A ι) (M : LPoset A κ) : LPoset A (ι ⊕ κ) where
  label := Sum.elim L.label M.label
  le := Sum.Lex L.le M.le
  le_refl := by rintro (i | j); exacts [.inl (L.le_refl i), .inr (M.le_refl j)]
  le_trans := by
    rintro (i | i) (j | j) (k | k) h h'
    · exact .inl (L.le_trans (Sum.lex_inl_inl.mp h) (Sum.lex_inl_inl.mp h'))
    · exact Sum.Lex.sep _ _
    · cases h'
    · exact Sum.Lex.sep _ _
    · cases h
    · cases h
    · cases h'
    · exact .inr (M.le_trans (Sum.lex_inr_inr.mp h) (Sum.lex_inr_inr.mp h'))
  le_antisymm := by
    rintro (i | i) (j | j) h h'
    · exact congrArg Sum.inl (L.le_antisymm (Sum.lex_inl_inl.mp h) (Sum.lex_inl_inl.mp h'))
    · cases h'
    · cases h
    · exact congrArg Sum.inr (M.le_antisymm (Sum.lex_inr_inr.mp h) (Sum.lex_inr_inr.mp h'))

/-- Disjoint (parallel) sum: elements of `L` and `M` are incomparable.
This is the paper's `α ∥ β` before the carrier is reindexed. -/
def lpar (L : LPoset A ι) (M : LPoset A κ) : LPoset A (ι ⊕ κ) where
  label := Sum.elim L.label M.label
  le := Sum.LiftRel L.le M.le
  le_refl := by rintro (i | j); exacts [.inl (L.le_refl i), .inr (M.le_refl j)]
  le_trans := by
    rintro (i | i) (j | j) (k | k) h h'
    · exact .inl (L.le_trans (Sum.liftRel_inl_inl.mp h) (Sum.liftRel_inl_inl.mp h'))
    · cases h'
    · cases h
    · cases h
    · cases h
    · cases h
    · cases h'
    · exact .inr (M.le_trans (Sum.liftRel_inr_inr.mp h) (Sum.liftRel_inr_inr.mp h'))
  le_antisymm := by
    rintro (i | i) (j | j) h h'
    · exact congrArg Sum.inl
        (L.le_antisymm (Sum.liftRel_inl_inl.mp h) (Sum.liftRel_inl_inl.mp h'))
    · cases h
    · cases h
    · exact congrArg Sum.inr
        (M.le_antisymm (Sum.liftRel_inr_inr.mp h) (Sum.liftRel_inr_inr.mp h'))

end LPoset

/-- A label- and order-preserving isomorphism of labelled posets. -/
structure LIso {A : Type u} {ι : Type v} {κ : Type w}
    (L : LPoset A ι) (M : LPoset A κ) where
  /-- The underlying bijection of carriers. -/
  toEquiv : ι ≃ κ
  /-- The bijection preserves labels. -/
  label_eq : ∀ i, M.label (toEquiv i) = L.label i
  /-- The bijection reflects and preserves the order. -/
  le_iff : ∀ i j, M.le (toEquiv i) (toEquiv j) ↔ L.le i j

namespace LIso

variable {A : Type u} {ι : Type v} {κ : Type w} {μ : Type x}
variable {L : LPoset A ι} {M : LPoset A κ} {N : LPoset A μ}

/-- The identity isomorphism. -/
def refl (L : LPoset A ι) : LIso L L := ⟨Equiv.refl _, fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- The inverse isomorphism. -/
def symm (f : LIso L M) : LIso M L where
  toEquiv := f.toEquiv.symm
  label_eq j := by simpa using (f.label_eq (f.toEquiv.symm j)).symm
  le_iff i j := by simpa using (f.le_iff (f.toEquiv.symm i) (f.toEquiv.symm j)).symm

/-- Composition of isomorphisms. -/
def trans (f : LIso L M) (g : LIso M N) : LIso L N where
  toEquiv := f.toEquiv.trans g.toEquiv
  label_eq i := by simpa using (g.label_eq (f.toEquiv i)).trans (f.label_eq i)
  le_iff i j := by simpa using (g.le_iff (f.toEquiv i) (f.toEquiv j)).trans (f.le_iff i j)

/-- Reindexing is an isomorphism. -/
def comap (L : LPoset A ι) (e : κ ≃ ι) : LIso (L.comap e) L :=
  ⟨e, fun _ => rfl, fun _ _ => Iff.rfl⟩

/-- Sequential composition is a congruence for isomorphism. -/
def lseq {M' : LPoset A ι} (f : LIso L M) (g : LIso N M') :
    LIso (L.lseq N) (M.lseq M') where
  toEquiv := Equiv.sumCongr f.toEquiv g.toEquiv
  label_eq := by rintro (i | i) <;> simp [LPoset.lseq, f.label_eq, g.label_eq]
  le_iff := by rintro (i | i) (j | j) <;> simp [LPoset.lseq, f.le_iff, g.le_iff]

/-- Parallel composition is a congruence for isomorphism. -/
def lpar {M' : LPoset A ι} (f : LIso L M) (g : LIso N M') :
    LIso (L.lpar N) (M.lpar M') where
  toEquiv := Equiv.sumCongr f.toEquiv g.toEquiv
  label_eq := by rintro (i | i) <;> simp [LPoset.lpar, f.label_eq, g.label_eq]
  le_iff := by rintro (i | i) (j | j) <;> simp [LPoset.lpar, f.le_iff, g.le_iff]

/-- Sequential composition is associative up to isomorphism. -/
def lseqAssoc (L : LPoset A ι) (M : LPoset A κ) (N : LPoset A μ) :
    LIso ((L.lseq M).lseq N) (L.lseq (M.lseq N)) where
  toEquiv := Equiv.sumAssoc _ _ _
  label_eq := by rintro ((i | i) | i) <;> rfl
  le_iff := by rintro ((i | i) | i) ((j | j) | j) <;> simp [LPoset.lseq, Equiv.sumAssoc]

/-- Parallel composition is associative up to isomorphism. -/
def lparAssoc (L : LPoset A ι) (M : LPoset A κ) (N : LPoset A μ) :
    LIso ((L.lpar M).lpar N) (L.lpar (M.lpar N)) where
  toEquiv := Equiv.sumAssoc _ _ _
  label_eq := by rintro ((i | i) | i) <;> rfl
  le_iff := by rintro ((i | i) | i) ((j | j) | j) <;> simp [LPoset.lpar, Equiv.sumAssoc]

/-- Parallel composition is commutative up to isomorphism. -/
def lparComm (L : LPoset A ι) (M : LPoset A κ) :
    LIso (L.lpar M) (M.lpar L) where
  toEquiv := Equiv.sumComm _ _
  label_eq := by rintro (i | i) <;> rfl
  le_iff := by rintro (i | i) (j | j) <;> simp [LPoset.lpar]

end LIso

end Isotope.Pomset
