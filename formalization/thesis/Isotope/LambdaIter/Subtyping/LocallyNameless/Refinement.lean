import Isotope.LambdaIter.Subtyping.LocallyNameless.TypedEquiv

/-!
# Proof-relevant directed refinement for lambda-iter

The generating theory is indexed by exact endpoint typing derivations.  Its
reflexive, transitive, compatible closure retains subtype witnesses, while the
existing typed equations are available in either direction.
-/

namespace Isotope.LambdaIter.Subtyping.LocallyNameless.Refinement

open Isotope.LambdaIter.LocallyNameless
open Isotope.LambdaIter.Subtyping.LocallyNameless

universe u w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {ε : Type r} [HasEff Φ ε]

set_option relaxedAutoImplicit true

/-- Primitive directed rewrites, indexed by their exact typing evidence. -/
structure Theory (Γ : LambdaIter.Ctx ν τ) where
  rel : {n : Nat} → {β : BoundCtx τ n} → {a b : Tm ν Φ n} → {A : τ} →
    HasType Φ Γ β a A → HasType Φ Γ β b A → Prop

/-- The least compatible preorder containing a primitive rewrite theory and
the typed equational theory. -/
inductive Deriv (pureEff : ε) (Γ : LambdaIter.Ctx ν τ) (R : Theory (Φ := Φ) Γ) :
    {n : Nat} → {β : BoundCtx τ n} → {a b : Tm ν Φ n} → {A : τ} →
      HasType Φ Γ β a A → HasType Φ Γ β b A → Type (max u w q r) where
  | refl (h : HasType Φ Γ β a A) : Deriv pureEff Γ R h h
  | trans (h : Deriv pureEff Γ R ha hm) (k : Deriv pureEff Γ R hm hb) :
      Deriv pureEff Γ R ha hb
  | axiom (h : R.rel ha hb) : Deriv pureEff Γ R ha hb
  | equiv (h : TypedEquiv.Deriv pureEff Γ ha hb) : Deriv pureEff Γ R ha hb
  | sub {n : Nat} {β : BoundCtx τ n} {a b : Tm ν Φ n} {A B : τ}
      {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
      (h : Deriv pureEff Γ R ha hb) (d : Subty A B) :
      Deriv pureEff Γ R (HasType.sub ha d) (HasType.sub hb d)
  | op (h : Deriv pureEff Γ R ha hb) :
      Deriv pureEff Γ R (.op ha) (.op hb)
  | let₁ (da : Deriv pureEff Γ R ha ha')
      (db : Deriv pureEff Γ R hb hb') :
      Deriv pureEff Γ R (.let₁ ha hb) (.let₁ ha' hb')
  | pair (da : Deriv pureEff Γ R ha ha')
      (db : Deriv pureEff Γ R hb hb') :
      Deriv pureEff Γ R (.pair ha hb) (.pair ha' hb')
  | let₂ (da : Deriv pureEff Γ R ha ha')
      (dc : Deriv pureEff Γ R hc hc') :
      Deriv pureEff Γ R (.let₂ ha hc) (.let₂ ha' hc')
  | inl (h : Deriv pureEff Γ R ha hb) :
      Deriv pureEff Γ R (HasType.inl (B := B) ha) (HasType.inl (B := B) hb)
  | inr (h : Deriv pureEff Γ R ha hb) :
      Deriv pureEff Γ R (HasType.inr (A := A) ha) (HasType.inr (A := A) hb)
  | case (de : Deriv pureEff Γ R he he')
      (dl : Deriv pureEff Γ R hl hl') (dr : Deriv pureEff Γ R hr hr') :
      Deriv pureEff Γ R (.case he hl hr) (.case he' hl' hr')
  | abort (h : Deriv pureEff Γ R ha hb) :
      Deriv pureEff Γ R (HasType.abort (C := C) ha) (HasType.abort (C := C) hb)
  | iter (da : Deriv pureEff Γ R ha ha')
      (db : Deriv pureEff Γ R hb hb') :
      Deriv pureEff Γ R (.iter ha hb) (.iter ha' hb')

variable {pureEff : ε} {Γ : LambdaIter.Ctx ν τ}
variable {R : Theory (Φ := Φ) Γ}
variable {n : Nat} {β : BoundCtx τ n} {a b c : Tm ν Φ n} {A : τ}
variable {ha : HasType Φ Γ β a A} {hb : HasType Φ Γ β b A}
variable {hc : HasType Φ Γ β c A}

/-- Proposition truncation of directed refinement at fixed typed endpoints. -/
abbrev Related (pureEff : ε) (Γ : LambdaIter.Ctx ν τ)
    (R : Theory (Φ := Φ) Γ) (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ β b A) : Prop := Nonempty (Deriv pureEff Γ R ha hb)

theorem Related.refl (h : HasType Φ Γ β a A) :
    Related pureEff Γ R h h := ⟨.refl h⟩

theorem Related.trans (hab : Related pureEff Γ R ha hb)
    (hbc : Related pureEff Γ R hb hc) : Related pureEff Γ R ha hc :=
  hab.elim fun dab => hbc.elim fun dbc => ⟨.trans dab dbc⟩

theorem Related.axiom (h : R.rel ha hb) : Related pureEff Γ R ha hb := ⟨.axiom h⟩

theorem Related.sub (h : Related pureEff Γ R ha hb) (d : Subty A B) :
    Related pureEff Γ R (.sub ha d) (.sub hb d) := h.map fun q => .sub q d

theorem Related.op {f : Φ} {a b : Tm ν Φ n}
    {ha : HasType Φ Γ β a (instrSrc f)} {hb : HasType Φ Γ β b (instrSrc f)}
    (h : Related pureEff Γ R ha hb) :
    Related pureEff Γ R (.op ha) (.op hb) := h.map .op

theorem Related.let₁ (ha : Related pureEff Γ R h₁ h₁')
    (hb : Related pureEff Γ R h₂ h₂') :
    Related pureEff Γ R (.let₁ h₁ h₂) (.let₁ h₁' h₂') :=
  ha.elim fun da => hb.elim fun db => ⟨.let₁ da db⟩

theorem Related.pair (ha : Related pureEff Γ R h₁ h₁')
    (hb : Related pureEff Γ R h₂ h₂') :
    Related pureEff Γ R (.pair h₁ h₂) (.pair h₁' h₂') :=
  ha.elim fun da => hb.elim fun db => ⟨.pair da db⟩

theorem Related.let₂ (ha : Related pureEff Γ R h₁ h₁')
    (hb : Related pureEff Γ R h₂ h₂') :
    Related pureEff Γ R (.let₂ h₁ h₂) (.let₂ h₁' h₂') :=
  ha.elim fun da => hb.elim fun db => ⟨.let₂ da db⟩

theorem Related.inl (h : Related pureEff Γ R ha hb) :
    Related pureEff Γ R (HasType.inl (B := B) ha) (HasType.inl (B := B) hb) :=
  h.map .inl

theorem Related.inr (h : Related pureEff Γ R ha hb) :
    Related pureEff Γ R (HasType.inr (A := B) ha) (HasType.inr (A := B) hb) :=
  h.map .inr

theorem Related.case (he : Related pureEff Γ R h₁ h₁')
    (hl : Related pureEff Γ R h₂ h₂') (hr : Related pureEff Γ R h₃ h₃') :
    Related pureEff Γ R (.case h₁ h₂ h₃) (.case h₁' h₂' h₃') :=
  he.elim fun de => hl.elim fun dl => hr.elim fun dr => ⟨.case de dl dr⟩

theorem Related.abort {a b : Tm ν Φ n}
    {ha : HasType Φ Γ β a TypeFormers.empty}
    {hb : HasType Φ Γ β b TypeFormers.empty}
    (h : Related pureEff Γ R ha hb) :
    Related pureEff Γ R (HasType.abort (C := B) ha) (HasType.abort (C := B) hb) :=
  h.map .abort

theorem Related.iter (ha : Related pureEff Γ R h₁ h₁')
    (hb : Related pureEff Γ R h₂ h₂') :
    Related pureEff Γ R (.iter h₁ h₂) (.iter h₁' h₂') :=
  ha.elim fun da => hb.elim fun db => ⟨.iter da db⟩

/-- Every typed equation induces refinement in its displayed direction. -/
theorem Related.ofEquiv (h : TypedEquiv.Related pureEff Γ ha hb) :
    Related pureEff Γ R ha hb := h.elim fun d => ⟨.equiv d⟩

/-- Typed equations induce refinement in both directions. -/
theorem Related.ofEquiv_both (h : TypedEquiv.Related pureEff Γ ha hb) :
    Related pureEff Γ R ha hb ∧ Related pureEff Γ R hb ha := by
  constructor
  · exact Related.ofEquiv h
  · exact h.elim fun d => ⟨.equiv (.symm d)⟩

/-- Equivalence generated by refinement is, by definition, mutual
refinement. -/
def Equivalent (pureEff : ε) (Γ : LambdaIter.Ctx ν τ)
    (R : Theory (Φ := Φ) Γ) (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ β b A) : Prop :=
  Related pureEff Γ R ha hb ∧ Related pureEff Γ R hb ha

theorem equivalent_iff_mutual :
    Equivalent pureEff Γ R ha hb ↔
      Related pureEff Γ R ha hb ∧ Related pureEff Γ R hb ha := Iff.rfl

theorem TypedEquiv.Related.toRefinementEquivalent
    (h : TypedEquiv.Related pureEff Γ ha hb) :
    Equivalent pureEff Γ R ha hb := Related.ofEquiv_both h

/-- The rewrite-free theory. -/
def EmptyTheory : Theory (Φ := Φ) Γ where
  rel := fun _ _ => False

/-- With no primitive directed rewrites, refinement collapses to the existing
typed equational theory. -/
def Deriv.toEquivOfEmpty : {n : Nat} → {β : BoundCtx τ n} →
    {a b : Tm ν Φ n} → {A : τ} →
    {ha : HasType Φ Γ β a A} → {hb : HasType Φ Γ β b A} →
    Deriv pureEff Γ (EmptyTheory (Γ := Γ)) ha hb →
      TypedEquiv.Deriv pureEff Γ ha hb
  | _, _, _, _, _, _, _, .refl h => .refl h
  | _, _, _, _, _, _, _, .trans h k => .trans h.toEquivOfEmpty k.toEquivOfEmpty
  | _, _, _, _, _, _, _, .axiom h => False.elim h
  | _, _, _, _, _, _, _, .equiv h => h
  | _, _, _, _, _, _, _, .sub h d => .sub h.toEquivOfEmpty d
  | _, _, _, _, _, _, _, .op h => .op h.toEquivOfEmpty
  | _, _, _, _, _, _, _, .let₁ ha hb => .let₁ ha.toEquivOfEmpty hb.toEquivOfEmpty
  | _, _, _, _, _, _, _, .pair ha hb => .pair ha.toEquivOfEmpty hb.toEquivOfEmpty
  | _, _, _, _, _, _, _, .let₂ ha hb => .let₂ ha.toEquivOfEmpty hb.toEquivOfEmpty
  | _, _, _, _, _, _, _, .inl h => .inl h.toEquivOfEmpty
  | _, _, _, _, _, _, _, .inr h => .inr h.toEquivOfEmpty
  | _, _, _, _, _, _, _, .case he hl hr =>
      .case he.toEquivOfEmpty hl.toEquivOfEmpty hr.toEquivOfEmpty
  | _, _, _, _, _, _, _, .abort h => .abort h.toEquivOfEmpty
  | _, _, _, _, _, _, _, .iter ha hb => .iter ha.toEquivOfEmpty hb.toEquivOfEmpty

theorem related_empty_iff_equiv :
    Related pureEff Γ (EmptyTheory (Γ := Γ)) ha hb ↔
      TypedEquiv.Related pureEff Γ ha hb := by
  constructor
  · exact fun h => h.elim fun d => ⟨d.toEquivOfEmpty⟩
  · exact Related.ofEquiv

theorem equivalent_empty_iff_equiv :
    Equivalent pureEff Γ (EmptyTheory (Γ := Γ)) ha hb ↔
      TypedEquiv.Related pureEff Γ ha hb := by
  rw [Equivalent, related_empty_iff_equiv, related_empty_iff_equiv]
  constructor
  · exact And.left
  · intro h
    exact ⟨h, h.elim fun d => ⟨.symm d⟩⟩

end Isotope.LambdaIter.Subtyping.LocallyNameless.Refinement
