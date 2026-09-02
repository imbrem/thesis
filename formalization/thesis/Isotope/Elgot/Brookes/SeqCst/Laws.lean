import Isotope.Elgot.Brookes.SeqCst.FullAbstraction

/-!
# Brookes's laws of parallel programming

> **Proposition 8.1** (Brookes, journal p. 152).  *The following laws are valid*:
> `skip;C ≡ C ≡ C;skip`, `(C₁;C₂);C₃ ≡ C₁;(C₂;C₃)`, `C ∥ skip ≡ C`,
> `C₁ ∥ C₂ ≡ C₂ ∥ C₁`, `(C₁∥C₂)∥C₃ ≡ C₁∥(C₂∥C₃)`,
> `(if B then C₁ else C₂);C ≡ if B then C₁;C else C₂;C`,
> `while B do C ≡ if B then C;while B do C else skip`,
> and `C₁;(C₂ ∥ C₃) ⊑ (C₁;C₂) ∥ C₃`, whence `C₁;C₂ ⊑ C₁ ∥ C₂`.

He proves them in one paragraph, "taking advantage of natural algebraic
identities involving `T₁;T₂`, `T₁ ∥ T₂` and `T*`"; the proofs here are ours.
Each law is given first as an equation between denotations and then, via
`fullAbstraction_eq`, as a contextual equivalence — which is what makes it usable
for compositional reasoning, and is Brookes's point.

`parU` is parallel composition at `PUnit`, which is what the language uses; its
laws are proved directly rather than transported across the product
isomorphisms of `Brookes.par`.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {Loc Val : Type u}

/-! ## Parallel composition of unit-valued computations -/

/-- Parallel composition at `PUnit`, the form the language uses. -/
def parU (x y : Comp Loc Val PUnit) : Comp Loc Val PUnit :=
  (fun _ ↦ PUnit.unit) <$> Brookes.par x y

theorem mem_parU_iff {x y : Comp Loc Val PUnit}
    {w : Trace (Store Loc Val × Store Loc Val)} {a : PUnit} :
    (w, a) ∈ parU x y ↔ ∃ w₀ t u, (t, PUnit.unit) ∈ x ∧ (u, PUnit.unit) ∈ y ∧
      Interleave t u w₀ ∧ (rewriting _).Refines w₀ w := by
  rw [parU, mem_map_iff]
  constructor
  · rintro ⟨p, -, hp⟩; exact mem_par_iff'.1 hp
  · intro h; exact ⟨(PUnit.unit, PUnit.unit), rfl, mem_par_iff'.2 h⟩

theorem mem_parU {x y : Comp Loc Val PUnit} {t u w : Trace (Store Loc Val × Store Loc Val)}
    (ht : (t, PUnit.unit) ∈ x) (hu : (u, PUnit.unit) ∈ y) (hi : Interleave t u w) :
    (w, PUnit.unit) ∈ parU x y :=
  mem_parU_iff.2 ⟨w, t, u, ht, hu, hi, .refl⟩

/-- `den (C₁ ∥ C₂)` is `parU` of the denotations. -/
theorem den_parU [DecidableEq Loc] [DecidableEq Val] (C₁ C₂ : Com Loc Val) :
    den (Com.par C₁ C₂) = parU (den C₁) (den C₂) := den_par C₁ C₂

/-! ## Structural laws for `parU` -/

theorem parU_mono {x x' y y' : Comp Loc Val PUnit} (hx : x ≤ x') (hy : y ≤ y') :
    parU x y ≤ parU x' y' := by
  apply le_of_mem
  intro w a hm
  obtain ⟨w₀, t, u, ht, hu, hi, hr⟩ := mem_parU_iff.1 hm
  exact mem_parU_iff.2 ⟨w₀, t, u, hx ht, hy hu, hi, hr⟩

/-- **`C₁ ∥ C₂ ≡ C₂ ∥ C₁`.** -/
theorem parU_comm (x y : Comp Loc Val PUnit) : parU x y = parU y x := by
  apply ext_mem
  intro w a
  rw [mem_parU_iff, mem_parU_iff]
  constructor
  · rintro ⟨w₀, t, u, ht, hu, hi, hr⟩; exact ⟨w₀, u, t, hu, ht, hi.swap, hr⟩
  · rintro ⟨w₀, t, u, ht, hu, hi, hr⟩; exact ⟨w₀, u, t, hu, ht, hi.swap, hr⟩

/-- **`(C₁ ∥ C₂) ∥ C₃ ≡ C₁ ∥ (C₂ ∥ C₃)`.**  Deferral of closure through the outer
shuffle (`SeqCst.defersPar`) is what makes the two bracketings agree. -/
theorem parU_assoc (x y z : Comp Loc Val PUnit) :
    parU (parU x y) z = parU x (parU y z) := by
  apply ext_mem
  intro w a
  rw [mem_parU_iff, mem_parU_iff]
  constructor
  · rintro ⟨w₀, t₁, t₂, ht₁, ht₂, hi, hr⟩
    obtain ⟨t₁₀, u₁, u₂, hu₁, hu₂, hi₁, hr₁⟩ := mem_parU_iff.1 ht₁
    obtain ⟨w₁, hi', hr'⟩ := defersPar.refines hr₁ hi
    obtain ⟨uv, huv, hw⟩ := interleave_assoc hi₁ hi'
    exact ⟨w₁, u₁, uv, hu₁, mem_parU hu₂ ht₂ huv, hw, hr'.trans hr⟩
  · rintro ⟨w₀, t₁, t₂, ht₁, ht₂, hi, hr⟩
    obtain ⟨t₂₀, u₁, u₂, hu₁, hu₂, hi₁, hr₁⟩ := mem_parU_iff.1 ht₂
    obtain ⟨w₁, hi', hr'⟩ := defersPar.refines_right hr₁ hi
    obtain ⟨uv, huv, hw⟩ := interleave_assoc hi₁.swap hi'.swap
    exact ⟨w₁, uv, u₂, mem_parU ht₁ hu₁ huv.swap, hu₂, hw.swap, hr'.trans hr⟩

/-! ## Sums and the Kleene star -/

@[simp] theorem power_zero (x : Comp Loc Val PUnit) : power x 0 = pure PUnit.unit := by
  rw [power]

@[simp] theorem power_succ (x : Comp Loc Val PUnit) (n : Nat) :
    power x (n + 1) = (x >>= fun _ ↦ power x n) := by rw [power]

theorem mem_star_iff {z : Comp Loc Val PUnit}
    {t : Trace (Store Loc Val × Store Loc Val)} {a : PUnit} :
    (t, a) ∈ star z ↔ ∃ n, (t, a) ∈ power z n := Brookes.mem_iUnion_iff

theorem union2_comm (x y : Comp Loc Val PUnit) : union2 x y = union2 y x := by
  apply ext_mem
  intro t a
  rw [mem_union2_iff, mem_union2_iff]
  exact Or.comm

theorem union2_bind (x y : Comp Loc Val PUnit) (f : PUnit → Comp Loc Val PUnit) :
    (union2 x y >>= f) = union2 (x >>= f) (y >>= f) := by
  apply ext_mem
  intro t a
  rw [mem_bind_iff, mem_union2_iff, mem_bind_iff, mem_bind_iff]
  constructor
  · rintro ⟨b, u, v, hu, hv, hr⟩
    rcases mem_union2_iff.1 hu with h | h
    · exact Or.inl ⟨b, u, v, h, hv, hr⟩
    · exact Or.inr ⟨b, u, v, h, hv, hr⟩
  · rintro (⟨b, u, v, hu, hv, hr⟩ | ⟨b, u, v, hu, hv, hr⟩)
    · exact ⟨b, u, v, mem_union2_iff.2 (Or.inl hu), hv, hr⟩
    · exact ⟨b, u, v, mem_union2_iff.2 (Or.inr hu), hv, hr⟩

/-- `T* = {ε}† ∪ T;T*`: the Kleene star unfolds. -/
theorem star_unfold (z : Comp Loc Val PUnit) :
    star z = union2 (pure PUnit.unit) (z >>= fun _ ↦ star z) := by
  apply ext_mem
  intro t a
  rw [mem_union2_iff, mem_star_iff]
  constructor
  · rintro ⟨n, hn⟩
    cases n with
    | zero => exact Or.inl hn
    | succ n =>
        rw [power_succ] at hn
        obtain ⟨b, u, v, hu, hv, hr⟩ := (mem_bind_iff _ _ _ _).1 hn
        exact Or.inr (mem_of_refines (mem_bind z _ hu (mem_star_iff.2 ⟨n, hv⟩)) hr)
  · rintro (h | h)
    · exact ⟨0, by rw [power_zero]; exact h⟩
    · obtain ⟨b, u, v, hu, hv, hr⟩ := (mem_bind_iff _ _ _ _).1 h
      obtain ⟨n, hn⟩ := mem_star_iff.1 hv
      refine ⟨n + 1, ?_⟩
      rw [power_succ]
      exact mem_of_refines (mem_bind z (fun _ ↦ power z n) hu hn) hr

/-! ## `skip` is a unit -/

variable [DecidableEq Loc] [DecidableEq Val]

theorem mem_den_skip_iff {u : Trace (Store Loc Val × Store Loc Val)} {a : PUnit} :
    (u, a) ∈ den (Com.skip : Com Loc Val) ↔
      ∃ μ : Store Loc Val, (rewriting _).Refines [(μ, μ)] u := by
  rw [den_skip, test, mem_atom_iff]
  constructor
  · rintro ⟨μ, ν, ⟨-, rfl⟩, hr⟩; exact ⟨ν, hr⟩
  · rintro ⟨μ, hr⟩; exact ⟨μ, μ, ⟨rfl, rfl⟩, hr⟩

theorem mem_den_skip (μ : Store Loc Val) (a : PUnit) :
    ([(μ, μ)], a) ∈ den (Com.skip : Com Loc Val) := mem_den_skip_iff.2 ⟨μ, .refl⟩

/-- Every trace of `skip` is a sequence of stutters. -/
theorem den_skip_stutters {u : Trace (Store Loc Val × Store Loc Val)} {a : PUnit}
    (h : (u, a) ∈ den (Com.skip : Com Loc Val)) : ∀ p ∈ u, p.1 = p.2 := by
  obtain ⟨μ, hr⟩ := mem_den_skip_iff.1 h
  exact compat_eq_of_refines_nil
    ((Relation.ReflTransGen.single (Step.stutter μ [])).trans hr)

/-- **`skip; C ≡ C`.**  Needs `C` to be `ε`-free, which every command is. -/
theorem skip_bind {x : Comp Loc Val PUnit}
    (hx : (([] : Trace (Store Loc Val × Store Loc Val)), PUnit.unit) ∉ x) :
    (den (Com.skip : Com Loc Val) >>= fun _ ↦ x) = x := by
  apply ext_mem
  intro t a
  rw [mem_bind_iff]
  constructor
  · rintro ⟨b, u, v, hu, hv, hr⟩
    refine mem_of_refines hv (Relation.ReflTransGen.trans ?_ hr)
    have hi : Interleave v u (u ++ v) := by
      have := (Interleave.nil_left u).appendCompat (Interleave.nil_right v)
      rwa [List.nil_append, List.append_nil] at this
    exact interleave_stutters_refines hi (den_skip_stutters hu)
  · intro ht
    rcases List.eq_nil_or_concat t with rfl | ⟨t', p, rfl⟩
    · exact absurd ht hx
    · rw [List.concat_eq_append] at ht ⊢
      rcases t' with _ | ⟨q, t''⟩
      · obtain ⟨μ, ρ⟩ := p
        exact ⟨PUnit.unit, [(μ, μ)], [(μ, ρ)], mem_den_skip μ PUnit.unit, ht,
          .single (Step.mumble μ μ ρ [])⟩
      · obtain ⟨μ, ρ⟩ := q
        refine ⟨PUnit.unit, [(μ, μ)], (μ, ρ) :: t'' ++ [p], mem_den_skip μ PUnit.unit, ht, ?_⟩
        exact .single (Step.mumble μ μ ρ (t'' ++ [p]))

/-- **`C; skip ≡ C`.** -/
theorem bind_skip {x : Comp Loc Val PUnit}
    (hx : (([] : Trace (Store Loc Val × Store Loc Val)), PUnit.unit) ∉ x) :
    (x >>= fun _ ↦ den (Com.skip : Com Loc Val)) = x := by
  apply ext_mem
  intro t a
  rw [mem_bind_iff]
  constructor
  · rintro ⟨b, u, v, hu, hv, hr⟩
    refine mem_of_refines hu (Relation.ReflTransGen.trans ?_ hr)
    exact interleave_stutters_refines (Interleave.append u v) (den_skip_stutters hv)
  · intro ht
    rcases List.eq_nil_or_concat t with rfl | ⟨t', p, rfl⟩
    · exact absurd ht hx
    · rw [List.concat_eq_append] at ht ⊢
      obtain ⟨μ, ρ⟩ := p
      refine ⟨PUnit.unit, t' ++ [(μ, ρ)], [(ρ, ρ)], ht, mem_den_skip ρ PUnit.unit, ?_⟩
      rw [List.append_assoc]
      exact .single ((rewriting _).step_appendLeft t' (Step.mumble μ ρ ρ []))

/-- **`C ∥ skip ≡ C`.** -/
theorem parU_skip {x : Comp Loc Val PUnit}
    (hx : (([] : Trace (Store Loc Val × Store Loc Val)), PUnit.unit) ∉ x) :
    parU x (den (Com.skip : Com Loc Val)) = x := by
  apply ext_mem
  intro w a
  rw [mem_parU_iff]
  constructor
  · rintro ⟨w₀, t, u, ht, hu, hi, hr⟩
    exact mem_of_refines ht
      ((interleave_stutters_refines hi (den_skip_stutters hu)).trans hr)
  · intro hw
    rcases List.eq_nil_or_concat w with rfl | ⟨w', p, rfl⟩
    · exact absurd hw hx
    · rw [List.concat_eq_append] at hw ⊢
      rcases w' with _ | ⟨q, w''⟩
      · obtain ⟨μ, ρ⟩ := p
        exact ⟨(μ, μ) :: [(μ, ρ)], [(μ, ρ)], [(μ, μ)], hw, mem_den_skip μ PUnit.unit,
          Interleave.right (Interleave.nil_right _), .single (Step.mumble μ μ ρ [])⟩
      · obtain ⟨μ, ρ⟩ := q
        refine ⟨(μ, μ) :: ((μ, ρ) :: w'' ++ [p]), (μ, ρ) :: w'' ++ [p], [(μ, μ)], hw,
          mem_den_skip μ PUnit.unit, Interleave.right (Interleave.nil_right _), ?_⟩
        exact .single (Step.mumble μ μ ρ (w'' ++ [p]))

/-! ## The laws, as equations between denotations -/

/-- **`skip; C ≡ C`** (Brookes, Proposition 8.1). -/
theorem den_skip_seq (C : Com Loc Val) : den (Com.seq .skip C) = den C := by
  rw [den_seq]; exact skip_bind (nil_not_mem_den C PUnit.unit)

/-- **`C; skip ≡ C`** (Brookes, Proposition 8.1). -/
theorem den_seq_skip (C : Com Loc Val) : den (Com.seq C .skip) = den C := by
  rw [den_seq]; exact bind_skip (nil_not_mem_den C PUnit.unit)

/-- **`(C₁;C₂);C₃ ≡ C₁;(C₂;C₃)`** (Brookes, Proposition 8.1). -/
theorem den_seq_assoc (C₁ C₂ C₃ : Com Loc Val) :
    den (Com.seq (Com.seq C₁ C₂) C₃) = den (Com.seq C₁ (Com.seq C₂ C₃)) := by
  rw [den_seq, den_seq, den_seq, den_seq]
  exact bind_assoc_eq _ _ _

/-- **`C ∥ skip ≡ C`** (Brookes, Proposition 8.1). -/
theorem den_par_skip (C : Com Loc Val) : den (Com.par C .skip) = den C := by
  rw [den_parU]; exact parU_skip (nil_not_mem_den C PUnit.unit)

/-- **`C₁ ∥ C₂ ≡ C₂ ∥ C₁`** (Brookes, Proposition 8.1). -/
theorem den_par_comm (C₁ C₂ : Com Loc Val) :
    den (Com.par C₁ C₂) = den (Com.par C₂ C₁) := by
  rw [den_parU, den_parU]; exact parU_comm _ _

/-- **`(C₁ ∥ C₂) ∥ C₃ ≡ C₁ ∥ (C₂ ∥ C₃)`** (Brookes, Proposition 8.1). -/
theorem den_par_assoc (C₁ C₂ C₃ : Com Loc Val) :
    den (Com.par (Com.par C₁ C₂) C₃) = den (Com.par C₁ (Com.par C₂ C₃)) := by
  rw [den_parU, den_parU, den_parU, den_parU]; exact parU_assoc _ _ _

/-- **`C₁; (C₂ ∥ C₃) ⊑ (C₁; C₂) ∥ C₃`** (Brookes, journal p. 152). -/
theorem den_seq_par_le (C₁ C₂ C₃ : Com Loc Val) :
    den (Com.seq C₁ (Com.par C₂ C₃)) ≤ den (Com.par (Com.seq C₁ C₂) C₃) := by
  rw [den_seq, den_parU, den_parU, den_seq]
  apply le_of_mem
  intro w a hm
  obtain ⟨b, u, v', hu, hv', hr⟩ := (mem_bind_iff _ _ _ _).1 hm
  obtain ⟨v₀, t, v, ht, hv, hi, hr'⟩ := mem_parU_iff.1 hv'
  refine mem_of_refines (mem_parU (mem_bind _ _ hu ht) hv
    ((Interleave.nil_right u).appendCompat hi)) ?_
  exact ((rewriting _).refines_appendLeft u hr').trans hr

/-- **`C₁; C₂ ⊑ C₁ ∥ C₂`** (Brookes, journal p. 152), the derived law. -/
theorem den_seq_le_par (C₁ C₂ : Com Loc Val) :
    den (Com.seq C₁ C₂) ≤ den (Com.par C₁ C₂) := by
  rw [den_seq, den_parU]
  apply le_of_mem
  intro w a hm
  obtain ⟨b, u, v, hu, hv, hr⟩ := (mem_bind_iff _ _ _ _).1 hm
  exact mem_of_refines (mem_parU hu hv (Interleave.append u v)) hr

/-! ## Unfolding a loop -/

/-- **`while B do C ≡ if B then C; while B do C else skip`** (Brookes,
Proposition 8.1). -/
theorem den_wh_unfold (b : BExp Loc Val) (C : Com Loc Val) :
    den (Com.wh b C) = den (Com.ite b (Com.seq C (Com.wh b C)) .skip) := by
  have hW : den (Com.wh b C)
      = (star (test b.eval >>= fun _ ↦ den C) >>= fun _ ↦ test (BExp.neg b).eval) :=
    den_wh b C
  have h1 : (star (test b.eval >>= fun _ ↦ den C) >>= fun _ ↦ test (BExp.neg b).eval)
      = union2 (test (BExp.neg b).eval)
        ((test b.eval >>= fun _ ↦ den C) >>= fun _ ↦ den (Com.wh b C)) := by
    rw [star_unfold, union2_bind, pure_bind_eq, bind_assoc_eq, ← hW]
  rw [den_ite, den_seq, bind_skip (x := test (BExp.neg b).eval) (nil_not_mem_atom PUnit.unit)]
  conv_lhs => rw [hW, h1]
  rw [union2_comm, bind_assoc_eq]

/-! ## The laws, as contextual equivalences -/

section Contextual

variable [Fintype Loc]

/- The `Fintype Loc` instance is used only through `fullAbstraction_eq`, whose
proof needs the separating contexts to be definable. -/
set_option linter.unusedFintypeInType false

theorem ctxEq_skip_seq (C : Com Loc Val) : CtxEq (Com.seq .skip C) C :=
  fullAbstraction_eq.1 (den_skip_seq C)

theorem ctxEq_seq_skip (C : Com Loc Val) : CtxEq (Com.seq C .skip) C :=
  fullAbstraction_eq.1 (den_seq_skip C)

theorem ctxEq_seq_assoc (C₁ C₂ C₃ : Com Loc Val) :
    CtxEq (Com.seq (Com.seq C₁ C₂) C₃) (Com.seq C₁ (Com.seq C₂ C₃)) :=
  fullAbstraction_eq.1 (den_seq_assoc C₁ C₂ C₃)

theorem ctxEq_par_skip (C : Com Loc Val) : CtxEq (Com.par C .skip) C :=
  fullAbstraction_eq.1 (den_par_skip C)

theorem ctxEq_par_comm (C₁ C₂ : Com Loc Val) :
    CtxEq (Com.par C₁ C₂) (Com.par C₂ C₁) :=
  fullAbstraction_eq.1 (den_par_comm C₁ C₂)

theorem ctxEq_par_assoc (C₁ C₂ C₃ : Com Loc Val) :
    CtxEq (Com.par (Com.par C₁ C₂) C₃) (Com.par C₁ (Com.par C₂ C₃)) :=
  fullAbstraction_eq.1 (den_par_assoc C₁ C₂ C₃)

theorem ctxEq_wh_unfold (b : BExp Loc Val) (C : Com Loc Val) :
    CtxEq (Com.wh b C) (Com.ite b (Com.seq C (Com.wh b C)) .skip) :=
  fullAbstraction_eq.1 (den_wh_unfold b C)

theorem ctxLe_seq_le_par (C₁ C₂ : Com Loc Val) :
    CtxLe (Com.seq C₁ C₂) (Com.par C₁ C₂) :=
  fullAbstraction.1 (den_seq_le_par C₁ C₂)

end Contextual

end SeqCst

end Isotope.Elgot.Brookes
