import Isotope.Elgot.TraceSet.Iteration

/-!
# Nondeterminism: unions, monotonicity, and iteration

Trace sets are ordered by inclusion, which is the refinement order of
nondeterministic choice.  This file records how `∪`, `⋃`, `•`, `>>=` and `iter`
interact with that order.

Iteration is only *lax* with respect to unions of bodies: every run of `f` or of
`g` is a run of `fun a ↦ f a ∪ g a`, but the converse fails because a single run
of the union may alternate between the two bodies.
-/

namespace Isotope.Elgot

universe u

namespace TraceSet

variable {E T A B C : Type u}

section Order

@[refl] theorem Subset.refl (x : TraceSet E T A) : x ⊆ x := fun _ hu ↦ hu

theorem Subset.trans {x y z : TraceSet E T A} (hxy : x ⊆ y) (hyz : y ⊆ z) : x ⊆ z :=
  fun u hu ↦ hyz u (hxy u hu)

theorem empty_subset (x : TraceSet E T A) : (∅ : TraceSet E T A) ⊆ x := fun _ hu ↦ hu.elim

theorem subset_union_left (x y : TraceSet E T A) : x ⊆ x ∪ y := fun _ hu ↦ Or.inl hu

theorem subset_union_right (x y : TraceSet E T A) : y ⊆ x ∪ y := fun _ hu ↦ Or.inr hu

theorem union_subset {x y z : TraceSet E T A} (hx : x ⊆ z) (hy : y ⊆ z) : x ∪ y ⊆ z :=
  fun u hu ↦ hu.elim (hx u) (hy u)

@[simp] theorem empty_union (x : TraceSet E T A) : (∅ : TraceSet E T A) ∪ x = x := by
  apply ext
  intro u
  exact ⟨fun hu ↦ hu.elim (fun h ↦ h.elim) id, Or.inr⟩

@[simp] theorem union_empty (x : TraceSet E T A) : x ∪ (∅ : TraceSet E T A) = x := by
  apply ext
  intro u
  exact ⟨fun hu ↦ hu.elim id (fun h ↦ h.elim), Or.inl⟩

theorem union_comm (x y : TraceSet E T A) : x ∪ y = y ∪ x := by
  apply ext
  intro u
  exact ⟨fun hu ↦ hu.symm, fun hu ↦ hu.symm⟩

theorem union_self (x : TraceSet E T A) : x ∪ x = x := by
  apply ext
  intro u
  exact ⟨fun hu ↦ hu.elim id id, Or.inl⟩

end Order

section Smul

variable [Mul E] [SMul E T]

theorem smul_mono {x y : TraceSet E T A} (e : E) (h : x ⊆ y) : e • x ⊆ e • y := by
  intro u hu
  rcases mem_smul.1 hu with ⟨v, hv, rfl⟩
  exact mem_smul.2 ⟨v, h v hv, rfl⟩

@[simp] theorem smul_empty (e : E) : e • (∅ : TraceSet E T A) = ∅ := by
  apply ext
  intro u
  exact ⟨fun hu ↦ (mem_smul.1 hu).elim (fun _ h ↦ h.1.elim), fun hu ↦ hu.elim⟩

theorem smul_union (e : E) (x y : TraceSet E T A) : e • (x ∪ y) = e • x ∪ e • y := by
  apply ext
  intro u
  constructor
  · intro hu
    rcases mem_smul.1 hu with ⟨v, hv, rfl⟩
    exact hv.elim (fun h ↦ Or.inl (mem_smul.2 ⟨v, h, rfl⟩))
      (fun h ↦ Or.inr (mem_smul.2 ⟨v, h, rfl⟩))
  · rintro (hu | hu) <;> rcases mem_smul.1 hu with ⟨v, hv, rfl⟩
    · exact mem_smul.2 ⟨v, Or.inl hv, rfl⟩
    · exact mem_smul.2 ⟨v, Or.inr hv, rfl⟩

theorem bindTrace_mono {v : Trace E T A} {f g : A → TraceSet E T B} (h : ∀ a, f a ⊆ g a) :
    bindTrace v f ⊆ bindTrace v g := by
  cases v with
  | done a e => exact smul_mono e (h a)
  | inf t => exact fun _ hu ↦ hu

theorem bindTrace_union (v : Trace E T A) (f g : A → TraceSet E T B) :
    bindTrace v (fun a ↦ f a ∪ g a) = bindTrace v f ∪ bindTrace v g := by
  cases v with
  | done a e => exact smul_union e (f a) (g a)
  | inf t => exact (union_self _).symm

end Smul

section Bind

variable [One E] [Mul E] [SMul E T]

theorem bind_mono {x y : TraceSet E T A} {f g : A → TraceSet E T B} (hxy : x ⊆ y)
    (hfg : ∀ a, f a ⊆ g a) : (x >>= f) ⊆ (y >>= g) := by
  intro u hu
  rcases (mem_bind_iff' x f u).1 hu with ⟨v, hv, hw⟩
  exact (mem_bind_iff' y g u).2 ⟨v, hxy v hv, bindTrace_mono hfg u hw⟩

@[simp] theorem empty_bind (f : A → TraceSet E T B) :
    ((∅ : TraceSet E T A) >>= f) = ∅ := by
  apply ext
  intro u
  constructor
  · intro hu
    rcases (mem_bind_iff' _ f u).1 hu with ⟨v, hv, _⟩
    exact hv.elim
  · intro hu
    exact hu.elim

theorem union_bind (x y : TraceSet E T A) (f : A → TraceSet E T B) :
    ((x ∪ y) >>= f) = (x >>= f) ∪ (y >>= f) := by
  apply ext
  intro u
  constructor
  · intro hu
    rcases (mem_bind_iff' _ f u).1 hu with ⟨v, hv, hw⟩
    exact hv.elim (fun h ↦ Or.inl ((mem_bind_iff' x f u).2 ⟨v, h, hw⟩))
      (fun h ↦ Or.inr ((mem_bind_iff' y f u).2 ⟨v, h, hw⟩))
  · rintro (hu | hu)
    · rcases (mem_bind_iff' x f u).1 hu with ⟨v, hv, hw⟩
      exact (mem_bind_iff' _ f u).2 ⟨v, Or.inl hv, hw⟩
    · rcases (mem_bind_iff' y f u).1 hu with ⟨v, hv, hw⟩
      exact (mem_bind_iff' _ f u).2 ⟨v, Or.inr hv, hw⟩

theorem bind_union (x : TraceSet E T A) (f g : A → TraceSet E T B) :
    (x >>= fun a ↦ f a ∪ g a) = (x >>= f) ∪ (x >>= g) := by
  apply ext
  intro u
  constructor
  · intro hu
    rcases (mem_bind_iff' x _ u).1 hu with ⟨v, hv, hw⟩
    rw [bindTrace_union] at hw
    exact hw.elim (fun h ↦ Or.inl ((mem_bind_iff' x f u).2 ⟨v, hv, h⟩))
      (fun h ↦ Or.inr ((mem_bind_iff' x g u).2 ⟨v, hv, h⟩))
  · rintro (hu | hu)
    · rcases (mem_bind_iff' x f u).1 hu with ⟨v, hv, hw⟩
      refine (mem_bind_iff' x _ u).2 ⟨v, hv, ?_⟩
      rw [bindTrace_union]
      exact Or.inl hw
    · rcases (mem_bind_iff' x g u).1 hu with ⟨v, hv, hw⟩
      refine (mem_bind_iff' x _ u).2 ⟨v, hv, ?_⟩
      rw [bindTrace_union]
      exact Or.inr hw

theorem iUnion_bind {ι : Type u} (x : ι → TraceSet E T A) (f : A → TraceSet E T B) :
    (iUnion x >>= f) = iUnion (fun i ↦ x i >>= f) := by
  apply ext
  intro u
  constructor
  · intro hu
    rcases (mem_bind_iff' _ f u).1 hu with ⟨v, hv, hw⟩
    rcases mem_iUnion.1 hv with ⟨i, hi⟩
    exact mem_iUnion.2 ⟨i, (mem_bind_iff' (x i) f u).2 ⟨v, hi, hw⟩⟩
  · intro hu
    rcases mem_iUnion.1 hu with ⟨i, hi⟩
    rcases (mem_bind_iff' (x i) f u).1 hi with ⟨v, hv, hw⟩
    exact (mem_bind_iff' _ f u).2 ⟨v, mem_iUnion.2 ⟨i, hv⟩, hw⟩

end Bind

section Iteration

variable [Mul E] [SMul E T]

theorem iter_union_left (f g : A → TraceSet E T (B ⊕ A)) (a : A) :
    iter f a ⊆ iter (fun a ↦ f a ∪ g a) a :=
  iter_mono (fun a ↦ subset_union_left (f a) (g a)) a

theorem iter_union_right (f g : A → TraceSet E T (B ⊕ A)) (a : A) :
    iter g a ⊆ iter (fun a ↦ f a ∪ g a) a :=
  iter_mono (fun a ↦ subset_union_right (f a) (g a)) a

/-- Iteration is lax with respect to unions of bodies.  The converse inclusion is
false: a single run of the union may alternate between `f` and `g`. -/
theorem union_iter_subset_iter_union (f g : A → TraceSet E T (B ⊕ A)) (a : A) :
    iter f a ∪ iter g a ⊆ iter (fun a ↦ f a ∪ g a) a :=
  union_subset (iter_union_left f g a) (iter_union_right f g a)

@[simp] theorem iter_empty_body (a : A) :
    iter (fun _ : A ↦ (∅ : TraceSet E T (B ⊕ A))) a = ∅ := by
  apply ext
  intro u
  constructor
  · intro hu
    cases hu with
    | ret hs => exact hs.elim
    | div hs => exact hs.elim
    | more hs _ => exact hs.elim
  · intro hu
    exact hu.elim

end Iteration

end TraceSet

end Isotope.Elgot
