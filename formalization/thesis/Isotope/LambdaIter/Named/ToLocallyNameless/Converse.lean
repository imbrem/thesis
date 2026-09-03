import Isotope.LambdaIter.Named.ToLocallyNameless.Alpha

/-! # Limits and hypotheses for the converse alpha theorem -/

namespace Isotope.LambdaIter.Named.ToLocallyNameless


universe u v

/-- Whether the root is a `let₁` with an anonymous binder. This small
observable is enough to refute the unrestricted converse theorem. -/
def RootLetAnonymous : Named.Tm ν Φ → Prop
  | .let₁ none _ _ => True
  | _ => False

private theorem rootLetAnonymous_let₁ (x : Binder ν)
    (a b a' b' : Named.Tm ν Φ) :
    RootLetAnonymous (.let₁ x a b) ↔ RootLetAnonymous (.let₁ x a' b') := by
  cases x <;> rfl

/-- Alpha-equivalence cannot turn an anonymous binder into a named binder. -/
theorem alpha_rootLetAnonymous_iff [DecidableEq ν] {a b : Named.Tm ν Φ}
    (h : Alpha a b) : RootLetAnonymous a ↔ RootLetAnonymous b := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | op | pair | inl | inr | case | abort | iter |
      let₁Rename | let₂RenameLeft | let₂RenameRight |
      caseRenameLeft | caseRenameRight | iterRename => simp [RootLetAnonymous]
  | let₁ => apply rootLetAnonymous_let₁
  | let₂ => rfl

namespace ConverseCounterexample

abbrev Name := Bool
abbrev Op := Empty

def anonymous : Named.Tm Name Op := .let₁ none .unit .unit
def named : Named.Tm Name Op := .let₁ (some false) .unit .unit

/-- Erasing an unused binder name identifies these raw terms. -/
theorem translations_equal : translateClosed anonymous = translateClosed named := rfl

/-- The named alpha relation intentionally preserves anonymous-binder slots. -/
theorem not_alpha : ¬Alpha anonymous named := by
  intro h
  have := alpha_rootLetAnonymous_iff h
  simpa [anonymous, named, RootLetAnonymous] using this

/-- Therefore equality of locally nameless translations does not imply the
current named alpha-equivalence on unrestricted raw terms. -/
theorem unrestricted_converse_false :
    translateClosed anonymous = translateClosed named ∧ ¬Alpha anonymous named :=
  ⟨translations_equal, not_alpha⟩

end ConverseCounterexample

/-- Corresponding terms have the same constructors and binder annotations;
variable names are deliberately left unconstrained. -/
inductive SameBinders {ν : Type u} {Φ : Type v} :
    Named.Tm ν Φ → Named.Tm ν Φ → Prop where
  | var (x y : ν) : SameBinders (.var x) (.var y)
  | op : SameBinders a b → SameBinders (.op f a) (.op f b)
  | let₁ : SameBinders a a' → SameBinders b b' →
      SameBinders (.let₁ x a b) (.let₁ x a' b')
  | unit : SameBinders .unit .unit
  | pair : SameBinders a a' → SameBinders b b' →
      SameBinders (.pair a b) (.pair a' b')
  | let₂ : SameBinders a a' → SameBinders b b' →
      SameBinders (.let₂ x y a b) (.let₂ x y a' b')
  | inl : SameBinders a b → SameBinders (.inl a) (.inl b)
  | inr : SameBinders a b → SameBinders (.inr a) (.inr b)
  | case : SameBinders e e' → SameBinders a a' → SameBinders b b' →
      SameBinders (.case e x a y b) (.case e' x a' y b')
  | abort : SameBinders a b → SameBinders (.abort a) (.abort b)
  | iter : SameBinders a a' → SameBinders b b' →
      SameBinders (.iter a x b) (.iter a' x b')

private theorem sumMapSucc_injective {n : Nat} {ν : Type*} :
    Function.Injective (Sum.map (Fin.succ : Fin n → Fin (n + 1)) (id : ν → ν)) := by
  intro a b h
  cases a <;> cases b <;> simp_all

/-- Resolving names in one fixed scope is injective, even in the presence of
shadowing: a binder position carries only one name. -/
theorem Scope.resolve_injective [DecidableEq ν] (ρ : Scope ν n) :
    Function.Injective ρ.resolve := by
  intro x y h
  induction ρ with
  | nil => simpa using h
  | push q ρ ih =>
      cases q with
      | none =>
          apply ih
          rw [Scope.resolve_push_none, Scope.resolve_push_none] at h
          exact sumMapSucc_injective h
      | some z =>
          by_cases hx : x = z
          · subst x
            by_cases hy : y = z
            · exact hy.symm
            · cases hr : ρ.resolve y <;>
                simp [Scope.resolve_push_ne _ hy, hr] at h
              exact (Fin.succ_ne_zero _) h.symm |>.elim
          · by_cases hy : y = z
            · subst y
              cases hr : ρ.resolve x <;>
                simp [Scope.resolve_push_ne _ hx, hr] at h
            · apply ih
              apply sumMapSucc_injective
              simpa [Scope.resolve_push_ne _ hx, Scope.resolve_push_ne _ hy] using h

/-- Once binder annotations agree, translation loses no information. Thus the
nontrivial converse problem is precisely the normalization of binder names. -/
theorem translate_injective_of_sameBinders {ν : Type u} {Φ : Type v} [DecidableEq ν]
    {a b : Named.Tm ν Φ} (hs : SameBinders a b) (ρ : Scope ν n)
    (ht : translate ρ a = translate ρ b) : a = b := by
  induction hs generalizing n with
  | var x y =>
      simp only [translate] at ht
      cases hx : ρ.lookup x with
      | none =>
          cases hy : ρ.lookup y with
          | none => simpa [hx, hy] using ht
          | some j => simp [hx, hy] at ht
      | some i =>
          cases hy : ρ.lookup y with
          | none => simp [hx, hy] at ht
          | some j =>
              have hij : i = j := by simpa [hx, hy] using ht
              apply congrArg Tm.var
              apply ρ.resolve_injective
              simp [Scope.resolve, hx, hy, hij]
  | op h ih =>
      simp only [translate] at ht
      injection ht with _ _ ht
      rw [ih ρ ht]
  | let₁ ha hb iha ihb =>
      simp only [translate] at ht
      injection ht with _ hta htb
      rw [iha ρ hta, ihb (.push _ ρ) htb]
  | unit => rfl
  | pair ha hb iha ihb =>
      simp only [translate] at ht
      injection ht with _ hta htb
      rw [iha ρ hta, ihb ρ htb]
  | let₂ ha hb iha ihb =>
      simp only [translate] at ht
      injection ht with _ hta htb
      rw [iha ρ hta, ihb (.push _ (.push _ ρ)) htb]
  | inl h ih | inr h ih | abort h ih =>
      simp only [translate] at ht
      injection ht with _ ht
      rw [ih ρ ht]
  | case he ha hb ihe iha ihb =>
      simp only [translate] at ht
      injection ht with _ hte hta htb
      rw [ihe ρ hte, iha (.push _ ρ) hta, ihb (.push _ ρ) htb]
  | iter ha hb iha ihb =>
      simp only [translate] at ht
      injection ht with _ hta htb
      rw [iha ρ hta, ihb (.push _ ρ) htb]

theorem alpha_of_sameBinders_translation_eq [DecidableEq ν]
    {a b : Named.Tm ν Φ} (hs : SameBinders a b)
    (ht : translateClosed a = translateClosed b) : Alpha a b := by
  rw [translate_injective_of_sameBinders hs .nil ht]
  exact .refl _

namespace Let₂RenameRegression

abbrev Name := Fin 3
abbrev Op := Empty

def x : Name := 0
def y : Name := 1

/-- If the right binder is the new left name, renaming the left binder changes
an occurrence from the older slot to the newer slot. -/
def targetCaptureBefore : Named.Tm Name Op :=
  .let₂ (some x) (some y) .unit (.var x)

def targetCaptureAfter : Named.Tm Name Op :=
  .let₂ (some y) (some y) .unit (.var y)

theorem target_capture_changes_translation :
    translateClosed targetCaptureBefore ≠ translateClosed targetCaptureAfter := by
  simp [targetCaptureBefore, targetCaptureAfter, translateClosed, translate, x, y,
    Scope.resolve, Scope.lookup]

/-- If the right binder is the old left name, substitution changes an
occurrence which actually referred to the newer/right binder. -/
def sourceShadowBefore : Named.Tm Name Op :=
  .let₂ (some x) (some x) .unit (.var x)

def sourceShadowAfter : Named.Tm Name Op :=
  .let₂ (some y) (some x) .unit (.var y)

theorem source_shadow_changes_translation :
    translateClosed sourceShadowBefore ≠ translateClosed sourceShadowAfter := by
  simp [sourceShadowBefore, sourceShadowAfter, translateClosed, translate, x, y,
    Scope.resolve, Scope.lookup]

/-- The repaired constructor's old-name sibling premise rejects the second
counterexample. -/
theorem source_shadow_violates_old_premise : ¬(some x : Binder Name) ≠ some x := by simp

/-- Its new-name sibling premise rejects the first counterexample. -/
theorem target_capture_violates_new_premise : ¬(some y : Binder Name) ≠ some y := by simp

end Let₂RenameRegression

end Isotope.LambdaIter.Named.ToLocallyNameless
