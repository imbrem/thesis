import Isotope.LambdaIter.Named.ToLocallyNameless

namespace Isotope.LambdaIter.Named.ToLocallyNameless

private theorem translate_subst_under_binder [DecidableEq ν]
    {ρ σ : Scope ν n} (x y : ν) (q : Binder ν) (b : Named.Tm ν Φ)
    (ih : ∀ {n} {ρ σ : Scope ν n},
      (¬b.Free y) → CaptureSafe (.var y) b →
      (∀ z, b.Free z → ρ.resolve z = σ.resolve (if x = z then y else z)) →
      translate ρ b = translate σ (Tm.subst x (.var y) b))
    (hfree : ¬b.Free y) (hsafe : CaptureSafe (.var y) b)
    (hqy : q ≠ some y)
    (hres : ∀ z, b.Free z → q ≠ some z →
      ρ.resolve z = σ.resolve (if x = z then y else z)) :
    translate (.push q ρ) b = translate (.push q σ)
      (if q = some x then b else Tm.subst x (.var y) b) := by
  by_cases hqx : q = some x
  · subst q
    rw [if_pos rfl]
    apply translate_congr
    intro z hz
    apply Scope.resolve_push_shadow
    intro hzx
    have hxz : x ≠ z := Ne.symm hzx
    simpa [hxz] using hres z hz (by
      intro h
      exact hxz (Option.some.inj h))
  · rw [if_neg hqx]
    apply ih hfree hsafe
    intro z hz
    by_cases hqz : q = some z
    · have hxz : x ≠ z := by
        intro e
        subst z
        exact hqx hqz
      rw [hqz]
      simp [hxz]
    · apply Scope.resolve_push_rename hqx hqy
      exact hres z hz hqz

private theorem translate_subst_under_binder_actual [DecidableEq ν]
    {ρ σ : Scope ν n} (x y : ν) (q : Binder ν) (b : Named.Tm ν Φ)
    (ih : ∀ {n} {ρ σ : Scope ν n},
      (¬b.Free y) → CaptureSafe (.var y) b →
      (∀ z, b.Free z → ρ.resolve z = σ.resolve (if x = z then y else z)) →
      translate ρ b = translate σ (Tm.subst x (.var y) b))
    (hfree : ¬b.Free y) (hsafe : CaptureSafe (.var y) b)
    (hqy : q ≠ some y)
    (hres : ∀ z, b.Free z → q ≠ some z →
      ρ.resolve z = σ.resolve (if x = z then y else z)) :
    translate (.push q ρ) b = translate (.push q σ)
      (if q.blocks x then b else Tm.subst x (.var y) b) := by
  have h := translate_subst_under_binder x y q b ih hfree hsafe hqy hres
  cases q with
  | none => simpa [Binder.blocks] using h
  | some w =>
      by_cases e : x = w
      · subst w
        simpa [Binder.blocks] using h
      · have ew : w ≠ x := fun h => e h.symm
        simpa [Binder.blocks, e, ew] using h

private theorem translate_subst_under_two_binders [DecidableEq ν]
    {ρ σ : Scope ν n} (x y : ν) (q r : Binder ν) (b : Named.Tm ν Φ)
    (ih : ∀ {n} {ρ σ : Scope ν n},
      (¬b.Free y) → CaptureSafe (.var y) b →
      (∀ z, b.Free z → ρ.resolve z = σ.resolve (if x = z then y else z)) →
      translate ρ b = translate σ (Tm.subst x (.var y) b))
    (hfree : ¬b.Free y) (hsafe : CaptureSafe (.var y) b)
    (hqy : q ≠ some y) (hry : r ≠ some y)
    (hres : ∀ z, b.Free z → q ≠ some z → r ≠ some z →
      ρ.resolve z = σ.resolve (if x = z then y else z)) :
    translate (.push r (.push q ρ)) b = translate (.push r (.push q σ))
      (if q = some x ∨ r = some x then b else Tm.subst x (.var y) b) := by
  by_cases hrx : r = some x
  · rw [if_pos (Or.inr hrx)]
    subst r
    apply translate_congr
    intro z hz
    apply Scope.resolve_push_shadow
    intro hzx
    by_cases hqz : q = some z
    · rw [hqz]; simp
    · apply Scope.resolve_push_eq
      have hxz : x ≠ z := Ne.symm hzx
      simpa [hxz] using hres z hz hqz (by
        intro e
        exact hzx (Option.some.inj e).symm)
  · by_cases hqx : q = some x
    · rw [if_pos (Or.inl hqx)]
      subst q
      apply translate_congr
      intro z hz
      by_cases hrz : r = some z
      · rw [hrz]; simp
      · apply Scope.resolve_push_eq
        apply Scope.resolve_push_shadow
        intro hzx
        have hxz : x ≠ z := Ne.symm hzx
        simpa [hxz] using hres z hz (by
          intro e
          exact hzx (Option.some.inj e).symm) hrz
    · rw [if_neg (fun h => h.elim hqx hrx)]
      apply ih hfree hsafe
      intro z hz
      by_cases hrz : r = some z
      · have hxz : x ≠ z := by
          intro e
          subst z
          exact hrx hrz
        rw [hrz]
        simp [hxz]
      · apply Scope.resolve_push_rename hrx hry
        by_cases hqz : q = some z
        · have hxz : x ≠ z := by
            intro e
            subst z
            exact hqx hqz
          rw [hqz]
          simp [hxz]
        · apply Scope.resolve_push_rename hqx hqy
          exact hres z hz hqz hrz

private theorem translate_subst_var [DecidableEq ν] {ρ σ : Scope ν n}
    (x y : ν) (a : Named.Tm ν Φ)
    (hfree : ¬a.Free y) (hsafe : CaptureSafe (.var y) a)
    (hres : ∀ z, a.Free z →
      ρ.resolve z = σ.resolve (if x = z then y else z)) :
    translate ρ a = translate σ (Tm.subst x (.var y) a) := by
  induction a generalizing n with
  | var z =>
      by_cases e : x = z
      · subst z
        simp only [Tm.subst_var_same, translate]
        rw [hres x rfl]
        simp
      · simp only [Tm.subst_var_ne e, translate]
        rw [hres z rfl]
        simp [e]
  | op f a ih =>
      simp only [Tm.subst, translate]
      rw [ih hfree hsafe (fun z hz => hres z hz)]
  | let₁ q a b iha ihb =>
      have hqy : q ≠ some y := by
        intro e
        exact hsafe y rfl (Or.inl e)
      have hfree_a : ¬a.Free y := fun h => hfree (Or.inl h)
      have hfree_b : ¬b.Free y := fun h => hfree (Or.inr ⟨hqy, h⟩)
      have hsafe_a : CaptureSafe (.var y) a := fun z hz hb =>
        hsafe z hz (Or.inr (Or.inl hb))
      have hsafe_b : CaptureSafe (.var y) b := fun z hz hb =>
        hsafe z hz (Or.inr (Or.inr hb))
      simp only [Tm.subst, translate]
      congr 1
      · exact iha hfree_a hsafe_a (fun z hz => hres z (Or.inl hz))
      · cases q with
        | none =>
            simpa using translate_subst_under_binder x y none b ihb hfree_b hsafe_b hqy
              (fun z hz hn => hres z (Or.inr ⟨hn, hz⟩))
        | some w =>
            by_cases e : w = x
            · subst w
              simpa [Binder.blocks] using translate_subst_under_binder x y (some x) b ihb hfree_b hsafe_b hqy
                (fun z hz hn => hres z (Or.inr ⟨hn, hz⟩))
            · have exw : x ≠ w := fun h => e h.symm
              simpa [e, exw, Binder.blocks] using
                translate_subst_under_binder x y (some w) b ihb
                hfree_b hsafe_b hqy (fun z hz hn => hres z (Or.inr ⟨hn, hz⟩))

  | unit => rfl
  | pair a b iha ihb =>
      simp only [Tm.subst, translate]
      congr 1
      · apply iha (fun ha => hfree (Or.inl ha))
          (fun z hz hb => hsafe z hz (Or.inl hb))
        exact fun z hz => hres z (Or.inl hz)
      · apply ihb (fun hb => hfree (Or.inr hb))
          (fun z hz hb => hsafe z hz (Or.inr hb))
        exact fun z hz => hres z (Or.inr hz)
  | let₂ q r a b iha ihb =>
      have hqy : q ≠ some y := by
        intro e
        exact hsafe y rfl (Or.inl e)
      have hry : r ≠ some y := by
        intro e
        exact hsafe y rfl (Or.inr (Or.inl e))
      have hfree_a : ¬a.Free y := fun h => hfree (Or.inl h)
      have hfree_b : ¬b.Free y := fun h => hfree (Or.inr ⟨hqy, hry, h⟩)
      have hsafe_a : CaptureSafe (.var y) a := fun z hz hb =>
        hsafe z hz (Or.inr (Or.inr (Or.inl hb)))
      have hsafe_b : CaptureSafe (.var y) b := fun z hz hb =>
        hsafe z hz (Or.inr (Or.inr (Or.inr hb)))
      simp only [Tm.subst, translate]
      congr 1
      · exact iha hfree_a hsafe_a (fun z hz => hres z (Or.inl hz))
      · have hb := translate_subst_under_two_binders x y q r b ihb
          hfree_b hsafe_b hqy hry
          (fun z hz hqz hrz => hres z (Or.inr ⟨hqz, hrz, hz⟩))
        cases q with
        | none =>
            cases r with
            | none => simpa [Binder.blocks] using hb
            | some v =>
                by_cases e : x = v
                · subst v
                  simpa [Binder.blocks] using hb
                · have ev : v ≠ x := fun h => e h.symm
                  simpa [Binder.blocks, e, ev] using hb
        | some u =>
            cases r with
            | none =>
                by_cases e : x = u
                · subst u
                  simpa [Binder.blocks] using hb
                · have eu : u ≠ x := fun h => e h.symm
                  simpa [Binder.blocks, e, eu] using hb
            | some v =>
                by_cases eu : x = u
                · subst u
                  simpa [Binder.blocks] using hb
                · have e'u : u ≠ x := fun h => eu h.symm
                  by_cases ev : x = v
                  · subst v
                    simpa [Binder.blocks, eu, e'u] using hb
                  · have e'v : v ≠ x := fun h => ev h.symm
                    simpa [Binder.blocks, eu, e'u, ev, e'v] using hb
  | inl a ih =>
      simp only [Tm.subst, translate]
      rw [ih hfree hsafe (fun z hz => hres z hz)]
  | inr a ih =>
      simp only [Tm.subst, translate]
      rw [ih hfree hsafe (fun z hz => hres z hz)]
  | case e q a r b ihe iha ihb =>
      have hqy : q ≠ some y := by
        intro h
        exact hsafe y rfl (Or.inl h)
      have hry : r ≠ some y := by
        intro h
        exact hsafe y rfl (Or.inr (Or.inl h))
      have hfree_e : ¬e.Free y := fun h => hfree (Or.inl h)
      have hfree_a : ¬a.Free y := fun h => hfree (Or.inr (Or.inl ⟨hqy, h⟩))
      have hfree_b : ¬b.Free y := fun h => hfree (Or.inr (Or.inr ⟨hry, h⟩))
      have hsafe_e : CaptureSafe (.var y) e := fun z hz hb =>
        hsafe z hz (Or.inr (Or.inr (Or.inl hb)))
      have hsafe_a : CaptureSafe (.var y) a := fun z hz hb =>
        hsafe z hz (Or.inr (Or.inr (Or.inr (Or.inl hb))))
      have hsafe_b : CaptureSafe (.var y) b := fun z hz hb =>
        hsafe z hz (Or.inr (Or.inr (Or.inr (Or.inr hb))))
      simp only [Tm.subst, translate]
      congr 1
      · exact ihe hfree_e hsafe_e (fun z hz => hres z (Or.inl hz))
      · exact translate_subst_under_binder_actual x y q a iha hfree_a hsafe_a hqy
          (fun z hz hn => hres z (Or.inr (Or.inl ⟨hn, hz⟩)))
      · exact translate_subst_under_binder_actual x y r b ihb hfree_b hsafe_b hry
          (fun z hz hn => hres z (Or.inr (Or.inr ⟨hn, hz⟩)))
  | abort a ih =>
      simp only [Tm.subst, translate]
      rw [ih hfree hsafe (fun z hz => hres z hz)]
  | iter a q b iha ihb =>
      have hqy : q ≠ some y := by
        intro e
        exact hsafe y rfl (Or.inl e)
      have hfree_a : ¬a.Free y := fun h => hfree (Or.inl h)
      have hfree_b : ¬b.Free y := fun h => hfree (Or.inr ⟨hqy, h⟩)
      have hsafe_a : CaptureSafe (.var y) a := fun z hz hb =>
        hsafe z hz (Or.inr (Or.inl hb))
      have hsafe_b : CaptureSafe (.var y) b := fun z hz hb =>
        hsafe z hz (Or.inr (Or.inr hb))
      simp only [Tm.subst, translate]
      congr 1
      · exact iha hfree_a hsafe_a (fun z hz => hres z (Or.inl hz))
      · cases q with
        | none =>
            simpa using translate_subst_under_binder x y none b ihb hfree_b hsafe_b hqy
              (fun z hz hn => hres z (Or.inr ⟨hn, hz⟩))
        | some w =>
            by_cases e : w = x
            · subst w
              simpa [Binder.blocks] using translate_subst_under_binder x y (some x) b ihb hfree_b hsafe_b hqy
                (fun z hz hn => hres z (Or.inr ⟨hn, hz⟩))
            · have exw : x ≠ w := fun h => e h.symm
              simpa [e, exw, Binder.blocks] using
                translate_subst_under_binder x y (some w) b ihb
                hfree_b hsafe_b hqy (fun z hz hn => hres z (Or.inr ⟨hn, hz⟩))

/-- Renaming a binder to a genuinely fresh, capture-safe name does not change
the locally nameless image of its body. -/
theorem translate_renameBinder [DecidableEq ν]
    (x y : ν) (b : Named.Tm ν Φ) (ρ : Scope ν n)
    (hfree : ¬b.Free y) (hsafe : CaptureSafe (.var y) b) :
    translate (.push (some x) ρ) b =
      translate (.push (some y) ρ) (Tm.substSafe x (.var y) b hsafe) := by
  apply translate_subst_var x y b hfree hsafe
  intro z hz
  by_cases e : x = z
  · subst z
    simp
  · have exz : z ≠ x := fun h => e h.symm
    have hzy : z ≠ y := by
      intro h
      subst z
      exact hfree hz
    rw [if_neg e]
    rw [Scope.resolve_push_ne _ exz, Scope.resolve_push_ne _ hzy]

/-- The analogous fact when a distinct newer sibling binder remains above the
renamed binder (the left-binder case of `let₂`). -/
private theorem translate_renameBinder_under [DecidableEq ν]
    (x z : ν) (q : Binder ν) (b : Named.Tm ν Φ) (ρ : Scope ν n)
    (hqx : q ≠ some x) (hqz : q ≠ some z) (hfree : ¬b.Free z)
    (hsafe : CaptureSafe (.var z) b) :
    translate (.push q (.push (some x) ρ)) b =
      translate (.push q (.push (some z) ρ))
        (Tm.substSafe x (.var z) b hsafe) := by
  apply translate_subst_var x z b hfree hsafe
  intro w hw
  by_cases hqw : q = some w
  · have hxw : x ≠ w := by
      intro e
      subst w
      exact hqx hqw
    have hzw : z ≠ w := by
      intro e
      subst w
      exact hqz hqw
    rw [hqw]
    simp [hxw, hzw]
  · apply Scope.resolve_push_rename hqx hqz
    by_cases e : x = w
    · subst w; simp
    · have e' : w ≠ x := fun h => e h.symm
      have hwz : w ≠ z := by
        intro h
        subst w
        exact hfree hw
      rw [if_neg e]
      rw [Scope.resolve_push_ne _ e', Scope.resolve_push_ne _ hwz]

/-- The independently defined named alpha-equivalence is contained in the
kernel of translation to locally nameless syntax. -/
theorem Alpha.toSameLocallyNameless [DecidableEq ν] {a b : Named.Tm ν Φ}
    (h : Alpha a b) : SameLocallyNameless a b := by
  induction h with
  | refl a => exact SameLocallyNameless.refl a
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | op _ ih => exact ih.op
  | let₁ _ _ ih₁ ih₂ => exact ih₁.let₁ ih₂
  | pair _ _ ih₁ ih₂ => exact ih₁.pair ih₂
  | let₂ _ _ ih₁ ih₂ => exact ih₁.let₂ ih₂
  | inl _ ih => exact ih.inl
  | inr _ ih => exact ih.inr
  | case _ _ _ ih₁ ih₂ ih₃ => exact SameLocallyNameless.case ih₁ ih₂ ih₃
  | abort _ ih => exact ih.abort
  | iter _ _ ih₁ ih₂ => exact ih₁.iter ih₂
  | let₁Rename hfree hsafe =>
      intro n ρ
      simp only [translate]
      rw [translate_renameBinder _ _ _ _ hfree hsafe]
  | let₂RenameLeft hsiblingOld hsiblingNew hfree hsafe =>
      intro n ρ
      simp only [translate]
      rw [translate_renameBinder_under _ _ _ _ _ hsiblingOld hsiblingNew hfree hsafe]
  | let₂RenameRight hfree hsafe =>
      intro n ρ
      simp only [translate]
      rw [translate_renameBinder _ _ _ _ hfree hsafe]
  | caseRenameLeft hfree hsafe =>
      intro n ρ
      simp only [translate]
      rw [translate_renameBinder _ _ _ _ hfree hsafe]
  | caseRenameRight hfree hsafe =>
      intro n ρ
      simp only [translate]
      rw [translate_renameBinder _ _ _ _ hfree hsafe]
  | iterRename hfree hsafe =>
      intro n ρ
      simp only [translate]
      rw [translate_renameBinder _ _ _ _ hfree hsafe]

end Isotope.LambdaIter.Named.ToLocallyNameless
