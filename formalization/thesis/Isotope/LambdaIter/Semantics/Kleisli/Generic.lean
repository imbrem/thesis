import Isotope.LambdaIter.Semantics.Denotation
import Isotope.LambdaIter.Subtyping.LocallyNameless.TypingSubst

/-!
# The exact judgment's metatheory commutes with the generic embedding

`HasType.toGeneric` embeds a coercion-free derivation into the proof-relevant
subtyping judgment without introducing a single `sub` node.  The renaming and
substitution operations of the two judgments are defined by literally the same
structural recursion (the subtyping versions carry one extra `sub` clause), so
the embedding commutes with all of them.

These lemmas are what let the soundness lemmas of
`Isotope/LambdaIter/Subtyping/Semantics/Soundness.lean`, which are stated for
the subtyping judgment and its canonical derivation constructors, be applied to
derivations that come from the exact judgment: the canonical *subtyping*
derivation built from two embedded derivations is itself the embedding of the
canonical *exact* derivation.
-/

namespace Isotope.LambdaIter.LocallyNameless

universe u v w q r

variable {τ : Type u} [TypeFormers τ] [Subtyping τ]
variable {ν : Type w} [DecidableEq ν]
variable {Φ : Type q} [HasTy Φ τ]
variable {Γ : LambdaIter.Ctx ν τ}

namespace TypedRenaming

/-- The exact and subtyping notions of typed bound renaming are the same data. -/
def toSubtyping {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    (ρ : TypedRenaming β β') : Subtyping.LocallyNameless.TypedRenaming β β' :=
  ⟨ρ.toFun, ρ.typed⟩

@[simp] theorem toSubtyping_toFun {n m : Nat} {β : BoundCtx τ n}
    {β' : BoundCtx τ m} (ρ : TypedRenaming β β') :
    ρ.toSubtyping.toFun = ρ.toFun := rfl

@[simp] theorem toSubtyping_up {n m : Nat} {β : BoundCtx τ n}
    {β' : BoundCtx τ m} (ρ : TypedRenaming β β') (A : τ) :
    (ρ.up A).toSubtyping = ρ.toSubtyping.up A := rfl

@[simp] theorem toSubtyping_succ {n : Nat} (β : BoundCtx τ n) (A : τ) :
    (TypedRenaming.succ β A).toSubtyping =
      Subtyping.LocallyNameless.TypedRenaming.succ β A := rfl

@[simp] theorem toSubtyping_underBinder {n : Nat} (β : BoundCtx τ n)
    (X Y : τ) :
    (TypedRenaming.underBinder β X Y).toSubtyping =
      Subtyping.LocallyNameless.TypedRenaming.underBinder β X Y := rfl

@[simp] theorem toSubtyping_underTwoBinders {n : Nat} (β : BoundCtx τ n)
    (X Y Z : τ) :
    (TypedRenaming.underTwoBinders β X Y Z).toSubtyping =
      Subtyping.LocallyNameless.TypedRenaming.underTwoBinders β X Y Z := rfl

end TypedRenaming

namespace HasType

section Constructors

variable {n : Nat} {β : BoundCtx τ n}

/-- The embedding is the identity on free variables. -/
@[simp] theorem toGeneric_fv {x : ν} {A : τ} (h : Γ.lookup x = some A) :
    (HasType.fv (Φ := Φ) (β := β) h).toGeneric =
      Subtyping.LocallyNameless.HasType.fv h := rfl

/-- The embedding is the identity on bound variables. -/
@[simp] theorem toGeneric_bv {i : Fin n} :
    (HasType.bv (Φ := Φ) (Γ := Γ) (β := β) (ι := i)).toGeneric =
      Subtyping.LocallyNameless.HasType.bv := rfl

/-- The embedding commutes with instruction application. -/
@[simp] theorem toGeneric_op {f : Φ} {a : Tm ν Φ n}
    (h : HasType Φ Γ β a (instrSrc f)) :
    (HasType.op h).toGeneric =
      Subtyping.LocallyNameless.HasType.op h.toGeneric := rfl

/-- The embedding commutes with `let`. -/
@[simp] theorem toGeneric_let₁ {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ (.snoc β A) b B) :
    (HasType.let₁ ha hb).toGeneric =
      Subtyping.LocallyNameless.HasType.let₁ ha.toGeneric hb.toGeneric := rfl

/-- The embedding is the identity on the unit introduction. -/
@[simp] theorem toGeneric_unit :
    (HasType.unit (Φ := Φ) (Γ := Γ) (β := β)).toGeneric =
      Subtyping.LocallyNameless.HasType.unit := rfl

/-- The embedding commutes with pairing. -/
@[simp] theorem toGeneric_pair {a b : Tm ν Φ n} {A B : τ}
    (ha : HasType Φ Γ β a A) (hb : HasType Φ Γ β b B) :
    (HasType.pair ha hb).toGeneric =
      Subtyping.LocallyNameless.HasType.pair ha.toGeneric hb.toGeneric := rfl

/-- The embedding commutes with pair elimination. -/
@[simp] theorem toGeneric_let₂ {a : Tm ν Φ n} {c : Tm ν Φ (n + 2)} {A B C : τ}
    (ha : HasType Φ Γ β a (TypeFormers.tensor A B))
    (hc : HasType Φ Γ (.snoc (.snoc β A) B) c C) :
    (HasType.let₂ ha hc).toGeneric =
      Subtyping.LocallyNameless.HasType.let₂ ha.toGeneric hc.toGeneric := rfl

/-- The embedding commutes with left injection. -/
@[simp] theorem toGeneric_inl {a : Tm ν Φ n} {A B : τ}
    (h : HasType Φ Γ β a A) :
    (HasType.inl (B := B) h).toGeneric =
      Subtyping.LocallyNameless.HasType.inl h.toGeneric := rfl

/-- The embedding commutes with right injection. -/
@[simp] theorem toGeneric_inr {b : Tm ν Φ n} {A B : τ}
    (h : HasType Φ Γ β b B) :
    (HasType.inr (A := A) h).toGeneric =
      Subtyping.LocallyNameless.HasType.inr h.toGeneric := rfl

/-- The embedding commutes with case analysis. -/
@[simp] theorem toGeneric_case {e : Tm ν Φ n} {l r : Tm ν Φ (n + 1)}
    {A B C : τ} (he : HasType Φ Γ β e (TypeFormers.coprod A B))
    (hl : HasType Φ Γ (.snoc β A) l C)
    (hr : HasType Φ Γ (.snoc β B) r C) :
    (HasType.case he hl hr).toGeneric =
      Subtyping.LocallyNameless.HasType.case he.toGeneric hl.toGeneric
        hr.toGeneric := rfl

/-- The embedding commutes with `abort`. -/
@[simp] theorem toGeneric_abort {a : Tm ν Φ n} {A : τ}
    (h : HasType Φ Γ β a (TypeFormers.empty : τ)) :
    (HasType.abort (C := A) h).toGeneric =
      Subtyping.LocallyNameless.HasType.abort h.toGeneric := rfl

/-- The embedding commutes with iteration. -/
@[simp] theorem toGeneric_iter {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)} {A B : τ}
    (ha : HasType Φ Γ β a A)
    (hb : HasType Φ Γ (.snoc β A) b (TypeFormers.coprod B A)) :
    (HasType.iter ha hb).toGeneric =
      Subtyping.LocallyNameless.HasType.iter ha.toGeneric hb.toGeneric := rfl

end Constructors

/-- The embedding commutes with transport along an equation between result
types. -/
theorem toGeneric_cast {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n} {A B : τ}
    (e : A = B) (h : HasType Φ Γ β t A) :
    (e ▸ h : HasType Φ Γ β t B).toGeneric = e ▸ h.toGeneric := by
  cases e; rfl

/-- The newest bound variable embeds to the newest bound variable. -/
@[simp] theorem toGeneric_newest {n : Nat} {β : BoundCtx τ n} {A : τ} :
    (HasType.newest (Φ := Φ) (Γ := Γ) (β := β) (A := A)).toGeneric =
      Subtyping.LocallyNameless.HasType.newest := rfl

/-- The next-to-newest bound variable embeds to its subtyping counterpart. -/
@[simp] theorem toGeneric_previous {n : Nat} {β : BoundCtx τ n} {A B : τ} :
    (HasType.previous (Φ := Φ) (Γ := Γ) (β := β) (A := A) (B := B)).toGeneric =
      Subtyping.LocallyNameless.HasType.previous := rfl

/-- Renaming commutes with the embedding. -/
theorem toGeneric_rename {n : Nat} {β : BoundCtx τ n} :
    ∀ {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) {m : Nat}
      {β' : BoundCtx τ m} (ρ : TypedRenaming β β'),
      (h.rename ρ).toGeneric = h.toGeneric.rename ρ.toSubtyping := by
  intro t A h
  induction h with
  | fv h => intro m β' ρ; rfl
  | @bv _ _ i => intro m β' ρ; exact toGeneric_cast (ρ.typed i) HasType.bv
  | op _ ih =>
      intro m β' ρ
      show Subtyping.LocallyNameless.HasType.op _ =
        Subtyping.LocallyNameless.HasType.op _
      exact congrArg _ (ih ρ)
  | let₁ _ _ iha ihb =>
      intro m β' ρ
      show Subtyping.LocallyNameless.HasType.let₁ _ _ =
        Subtyping.LocallyNameless.HasType.let₁ _ _
      congr 1
      · exact iha ρ
      · exact ihb (ρ.up _)
  | unit => intro m β' ρ; rfl
  | pair _ _ iha ihb =>
      intro m β' ρ
      show Subtyping.LocallyNameless.HasType.pair _ _ =
        Subtyping.LocallyNameless.HasType.pair _ _
      congr 1
      · exact iha ρ
      · exact ihb ρ
  | let₂ _ _ iha ihb =>
      intro m β' ρ
      show Subtyping.LocallyNameless.HasType.let₂ _ _ =
        Subtyping.LocallyNameless.HasType.let₂ _ _
      congr 1
      · exact iha ρ
      · exact ihb ((ρ.up _).up _)
  | inl _ ih =>
      intro m β' ρ
      show Subtyping.LocallyNameless.HasType.inl _ =
        Subtyping.LocallyNameless.HasType.inl _
      exact congrArg _ (ih ρ)
  | inr _ ih =>
      intro m β' ρ
      show Subtyping.LocallyNameless.HasType.inr _ =
        Subtyping.LocallyNameless.HasType.inr _
      exact congrArg _ (ih ρ)
  | case _ _ _ ihe ihl ihr =>
      intro m β' ρ
      show Subtyping.LocallyNameless.HasType.case _ _ _ =
        Subtyping.LocallyNameless.HasType.case _ _ _
      congr 1
      · exact ihe ρ
      · exact ihl (ρ.up _)
      · exact ihr (ρ.up _)
  | abort _ ih =>
      intro m β' ρ
      show Subtyping.LocallyNameless.HasType.abort _ =
        Subtyping.LocallyNameless.HasType.abort _
      exact congrArg _ (ih ρ)
  | iter _ _ iha ihb =>
      intro m β' ρ
      show Subtyping.LocallyNameless.HasType.iter _ _ =
        Subtyping.LocallyNameless.HasType.iter _ _
      congr 1
      · exact iha ρ
      · exact ihb (ρ.up _)

/-- Lifting commutes with the embedding. -/
@[simp] theorem toGeneric_lift {n : Nat} {β : BoundCtx τ n} {t : Tm ν Φ n}
    {A B : τ} (h : HasType Φ Γ β t A) :
    (h.lift (B := B)).toGeneric = h.toGeneric.lift := by
  simpa [HasType.lift, Subtyping.LocallyNameless.HasType.lift] using
    toGeneric_rename h (TypedRenaming.succ β B)

/-- Weakening under one binder commutes with the embedding. -/
@[simp] theorem toGeneric_underBinder {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ (n + 1)} {A X Y : τ} (h : HasType Φ Γ (.snoc β Y) t A) :
    (h.underBinder (X := X)).toGeneric = h.toGeneric.underBinder := by
  simpa [HasType.underBinder, Subtyping.LocallyNameless.HasType.underBinder]
    using toGeneric_rename h (TypedRenaming.underBinder β X Y)

/-- Weakening under two binders commutes with the embedding. -/
@[simp] theorem toGeneric_underTwoBinders {n : Nat} {β : BoundCtx τ n}
    {t : Tm ν Φ (n + 2)} {A X Y Z : τ}
    (h : HasType Φ Γ (.snoc (.snoc β Y) Z) t A) :
    (h.underTwoBinders (X := X)).toGeneric = h.toGeneric.underTwoBinders := by
  simpa [HasType.underTwoBinders,
    Subtyping.LocallyNameless.HasType.underTwoBinders] using
    toGeneric_rename h (TypedRenaming.underTwoBinders β X Y Z)

end HasType

namespace TypedSubst

/-- Embed a typed substitution slot by slot. -/
def toSubtyping {n m : Nat} {β : BoundCtx τ n} {β' : BoundCtx τ m}
    {σ : Fin n → Tm ν Φ m} (s : TypedSubst (Γ := Γ) β β' σ) :
    Subtyping.LocallyNameless.TypedSubst (Γ := Γ) β β' σ :=
  fun i => (s i).toGeneric

@[simp] theorem toSubtyping_up {n m : Nat} {β : BoundCtx τ n}
    {β' : BoundCtx τ m} {σ : Fin n → Tm ν Φ m}
    (s : TypedSubst (Γ := Γ) β β' σ) (A : τ) :
    (s.up A).toSubtyping = s.toSubtyping.up A := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · exact HasType.toGeneric_lift (s j)

end TypedSubst

namespace HasType

/-- Simultaneous substitution commutes with the embedding. -/
theorem toGeneric_bsubst {n : Nat} {β : BoundCtx τ n} :
    ∀ {t : Tm ν Φ n} {A : τ} (h : HasType Φ Γ β t A) {m : Nat}
      {β' : BoundCtx τ m} {σ : Fin n → Tm ν Φ m}
      (s : TypedSubst (Γ := Γ) β β' σ),
      (h.bsubst s).toGeneric = h.toGeneric.bsubst s.toSubtyping := by
  intro t A h
  induction h with
  | fv h => intro m β' σ s; rfl
  | bv => intro m β' σ s; rfl
  | op _ ih =>
      intro m β' σ s
      show Subtyping.LocallyNameless.HasType.op _ =
        Subtyping.LocallyNameless.HasType.op _
      exact congrArg _ (ih s)
  | let₁ _ _ iha ihb =>
      intro m β' σ s
      show Subtyping.LocallyNameless.HasType.let₁ _ _ =
        Subtyping.LocallyNameless.HasType.let₁ _ _
      congr 1
      · exact iha s
      · exact (ihb (s.up _)).trans (by rw [TypedSubst.toSubtyping_up])
  | unit => intro m β' σ s; rfl
  | pair _ _ iha ihb =>
      intro m β' σ s
      show Subtyping.LocallyNameless.HasType.pair _ _ =
        Subtyping.LocallyNameless.HasType.pair _ _
      congr 1
      · exact iha s
      · exact ihb s
  | let₂ _ _ iha ihb =>
      intro m β' σ s
      show Subtyping.LocallyNameless.HasType.let₂ _ _ =
        Subtyping.LocallyNameless.HasType.let₂ _ _
      congr 1
      · exact iha s
      · exact (ihb ((s.up _).up _)).trans (by
          rw [TypedSubst.toSubtyping_up, TypedSubst.toSubtyping_up])
  | inl _ ih =>
      intro m β' σ s
      show Subtyping.LocallyNameless.HasType.inl _ =
        Subtyping.LocallyNameless.HasType.inl _
      exact congrArg _ (ih s)
  | inr _ ih =>
      intro m β' σ s
      show Subtyping.LocallyNameless.HasType.inr _ =
        Subtyping.LocallyNameless.HasType.inr _
      exact congrArg _ (ih s)
  | case _ _ _ ihe ihl ihr =>
      intro m β' σ s
      show Subtyping.LocallyNameless.HasType.case _ _ _ =
        Subtyping.LocallyNameless.HasType.case _ _ _
      congr 1
      · exact ihe s
      · exact (ihl (s.up _)).trans (by rw [TypedSubst.toSubtyping_up])
      · exact (ihr (s.up _)).trans (by rw [TypedSubst.toSubtyping_up])
  | abort _ ih =>
      intro m β' σ s
      show Subtyping.LocallyNameless.HasType.abort _ =
        Subtyping.LocallyNameless.HasType.abort _
      exact congrArg _ (ih s)
  | iter _ _ iha ihb =>
      intro m β' σ s
      show Subtyping.LocallyNameless.HasType.iter _ _ =
        Subtyping.LocallyNameless.HasType.iter _ _
      congr 1
      · exact iha s
      · exact (ihb (s.up _)).trans (by rw [TypedSubst.toSubtyping_up])

/-- Opening the newest binder commutes with the embedding. -/
@[simp] theorem toGeneric_instantiate {n : Nat} {β : BoundCtx τ n} {A B : τ}
    {a : Tm ν Φ n} {b : Tm ν Φ (n + 1)}
    (hb : HasType Φ Γ (.snoc β A) b B) (ha : HasType Φ Γ β a A) :
    (hb.instantiate ha).toGeneric =
      hb.toGeneric.instantiate ha.toGeneric := by
  have h := toGeneric_bsubst hb (σ := Fin.cases a fun i => .bv i)
    (Fin.cases ha fun _ => HasType.bv)
  refine h.trans ?_
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end HasType

/-- Syntactic purity for the coercion-free calculus is syntactic purity for the
subtyping calculus: the two inductive definitions have the same clauses over the
same terms. -/
theorem Pure.toGeneric {ε : Type r} [HasEff Φ ε] {pureEff : ε} :
    ∀ {n : Nat} {t : Tm ν Φ n}, Pure (Φ := Φ) (ν := ν) pureEff t →
      Subtyping.LocallyNameless.Pure (Φ := Φ) (ν := ν) pureEff t := by
  intro n t h
  induction h with
  | fv => exact .fv
  | bv => exact .bv
  | op hf _ ih => exact .op hf ih
  | let₁ _ _ iha ihb => exact .let₁ iha ihb
  | unit => exact .unit
  | pair _ _ iha ihb => exact .pair iha ihb
  | let₂ _ _ iha ihb => exact .let₂ iha ihb
  | inl _ ih => exact .inl ih
  | inr _ ih => exact .inr ih
  | case _ _ _ ihe ihl ihr => exact .case ihe ihl ihr
  | abort _ ih => exact .abort ih

end Isotope.LambdaIter.LocallyNameless
