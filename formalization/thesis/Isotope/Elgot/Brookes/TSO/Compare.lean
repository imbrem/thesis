import Isotope.Elgot.Brookes.TSO.Examples

/-!
# Comparison with the sequential-consistency model

`Brookes/SeqCst.lean` is the standard Brookes model over states `Loc → Val`.
The TSO model of this directory is the *same* construction over the richer state
`St`, so there is an evident map between them: forget the write buffers.

`SeqCst.mapState` is that map for an arbitrary state abstraction `f : S → S'`.
It is a monad morphism on the nose (`mapState_pure`, `mapState_bind`), because a
state abstraction sends stutters to stutters and mumbles to mumbles.

Instantiated at `St.mem`, it says exactly what store buffering is:

* `toSeqCst_writeSC` / `toSeqCst_readSC` — the sequentially consistent fragment of
  the TSO model *is* the sequential-consistency model, on the nose.
* `toSeqCst_writeCore_le` — a TSO write abstracts to a **stutter**: below `pure`,
  invisible in the sequentially consistent view.
* `toSeqCst_writeCore_ne_writeSC` — and the abstraction is not degenerate, so
  the two writes remain different computations after it.

## What is *not* proved here

`mapState` is not shown to commute with `iter`.  It does commute laxly in the
easy direction, but the equation needs the approximant chain of
`Brookes/Iteration.lean` to be pushed through `List.map`, which is more work
than the comparison needs.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace SeqCst

variable {S S' : Type u} {A B : Type u}

/-- A state abstraction sends stutters to stutters and mumbles to mumbles. -/
theorem Step.map (f : S → S') {t t' : Trace (S × S)} (h : Step S t t') :
    Step S' (t.map (Prod.map f f)) (t'.map (Prod.map f f)) := by
  induction h with
  | stutter μ t => exact Step.stutter (f μ) _
  | mumble μ ρ θ t => exact Step.mumble (f μ) (f ρ) (f θ) _
  | cons p _ ih => exact Step.cons (Prod.map f f p) ih

/-- Hence a state abstraction preserves refinement. -/
theorem refines_map (f : S → S') {t t' : Trace (S × S)}
    (h : (rewriting S).Refines t t') :
    (rewriting S').Refines (t.map (Prod.map f f)) (t'.map (Prod.map f f)) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (Step.map f hstep)

/-- The image of a Brookes computation under a state abstraction. -/
def mapState (f : S → S') (x : Brookes (rewriting S) A) : Brookes (rewriting S') A :=
  close _ {p | ∃ t, (t, p.2) ∈ x ∧ p.1 = t.map (Prod.map f f)}

theorem mem_mapState_iff {f : S → S'} {x : Brookes (rewriting S) A}
    {t : Trace (S' × S')} {a : A} :
    (t, a) ∈ mapState f x ↔
      ∃ t₀, (t₀, a) ∈ x ∧ (rewriting S').Refines (t₀.map (Prod.map f f)) t := by
  constructor
  · rintro ⟨u, ⟨t₀, hmem, rfl⟩, hr⟩
    exact ⟨t₀, hmem, hr⟩
  · rintro ⟨t₀, hmem, hr⟩
    exact ⟨t₀.map (Prod.map f f), ⟨t₀, hmem, rfl⟩, hr⟩

theorem mem_mapState {f : S → S'} {x : Brookes (rewriting S) A} {t : Trace (S × S)} {a : A}
    (h : (t, a) ∈ x) : (t.map (Prod.map f f), a) ∈ mapState f x :=
  mem_mapState_iff.2 ⟨t, h, .refl⟩

theorem mapState_mono {f : S → S'} {x y : Brookes (rewriting S) A} (h : x ≤ y) :
    mapState f x ≤ mapState f y := by
  refine Brookes.le_of_mem fun t a hmem ↦ ?_
  obtain ⟨t₀, hm, hr⟩ := mem_mapState_iff.1 hmem
  exact mem_mapState_iff.2 ⟨t₀, h hm, hr⟩

/-- A state abstraction preserves `pure`. -/
@[simp] theorem mapState_pure (f : S → S') (a : A) :
    mapState f (pure a : Brookes (rewriting S) A) = pure a := by
  apply Brookes.ext_mem
  intro t b
  constructor
  · intro hmem
    obtain ⟨t₀, hm, hr⟩ := mem_mapState_iff.1 hmem
    obtain ⟨rfl, h0⟩ := (Brookes.mem_pure_iff a b t₀).1 hm
    exact (Brookes.mem_pure_iff b b t).2 ⟨rfl, (refines_map f h0).trans hr⟩
  · intro hmem
    obtain ⟨rfl, h0⟩ := (Brookes.mem_pure_iff a b t).1 hmem
    exact mem_mapState_iff.2 ⟨[], Brookes.mem_pure b, h0⟩

/-- A state abstraction preserves `bind`. -/
theorem mapState_bind (f : S → S') (x : Brookes (rewriting S) A)
    (g : A → Brookes (rewriting S) B) :
    mapState f (x >>= g) = mapState f x >>= fun a ↦ mapState f (g a) := by
  apply Brookes.ext_mem
  intro t b
  constructor
  · intro hmem
    obtain ⟨t₀, hm, hr⟩ := mem_mapState_iff.1 hmem
    obtain ⟨a, u, v, hu, hv, hr'⟩ := (Brookes.mem_bind_iff x g t₀ b).1 hm
    refine (Brookes.mem_bind_iff _ _ t b).2 ⟨a, u.map (Prod.map f f), v.map (Prod.map f f),
      mem_mapState hu, mem_mapState hv, ?_⟩
    rw [← List.map_append]
    exact (refines_map f hr').trans hr
  · intro hmem
    obtain ⟨a, u, v, hu, hv, hr⟩ := (Brookes.mem_bind_iff _ _ t b).1 hmem
    obtain ⟨u₀, hu₀, hru⟩ := mem_mapState_iff.1 hu
    obtain ⟨v₀, hv₀, hrv⟩ := mem_mapState_iff.1 hv
    refine mem_mapState_iff.2 ⟨u₀ ++ v₀, Brookes.mem_bind x g hu₀ hv₀, ?_⟩
    rw [List.map_append]
    exact (Rewriting.refines_append hru hrv).trans hr

end SeqCst

namespace TSO

variable {Tid Loc Val A : Type u}

/-- Forget the write buffers: the memory abstraction from the store-buffer TSO
model to the sequential-consistency model of `Brookes/SeqCst.lean`. -/
def toSeqCst (x : Comp Tid Loc Val A) : SeqCst.Comp Loc Val A :=
  SeqCst.mapState St.mem x

@[simp] theorem toSeqCst_pure (a : A) :
    toSeqCst (pure a : Comp Tid Loc Val A) = pure a := SeqCst.mapState_pure _ a

theorem toSeqCst_bind {B : Type u} (x : Comp Tid Loc Val A) (g : A → Comp Tid Loc Val B) :
    toSeqCst (x >>= g) = toSeqCst x >>= fun a ↦ toSeqCst (g a) :=
  SeqCst.mapState_bind _ x g

theorem toSeqCst_mono {x y : Comp Tid Loc Val A} (h : x ≤ y) : toSeqCst x ≤ toSeqCst y :=
  SeqCst.mapState_mono h

/-- The sequentially consistent write of the TSO model abstracts exactly to the
paper's `write`. -/
theorem toSeqCst_writeSC [DecidableEq Loc] (ℓ : Loc) (v : Val) :
    toSeqCst (Tid := Tid) (writeSC ℓ v) = SeqCst.write ℓ v := by
  apply Brookes.ext_mem
  intro t a
  constructor
  · intro hmem
    obtain ⟨t₀, hm, hr⟩ := SeqCst.mem_mapState_iff.1 hmem
    obtain ⟨u, ⟨s, hu⟩, hru⟩ := hm
    refine (SeqCst.mem_write_iff ℓ v t a).2 ⟨s.mem, ?_⟩
    refine Relation.ReflTransGen.trans ?_ hr
    have := SeqCst.refines_map (St.mem (Tid := Tid) (Loc := Loc) (Val := Val)) hru
    rwa [show u = [(s, s.setMem ℓ v)] from hu] at this
  · intro hmem
    obtain ⟨μ, hr⟩ := (SeqCst.mem_write_iff ℓ v t a).1 hmem
    refine SeqCst.mem_mapState_iff.2
      ⟨[((⟨μ, fun _ ↦ []⟩ : St Tid Loc Val), (⟨μ, fun _ ↦ []⟩ : St Tid Loc Val).setMem ℓ v)],
        mem_writeSC ℓ v _ a, hr⟩

/-- The sequentially consistent read of the TSO model abstracts exactly to
`SeqCst.read`. -/
theorem toSeqCst_readSC (ℓ : Loc) :
    toSeqCst (readSC (Tid := Tid) (Val := Val) ℓ) = SeqCst.read ℓ := by
  apply Brookes.ext_mem
  intro t a
  constructor
  · intro hmem
    obtain ⟨t₀, hm, hr⟩ := SeqCst.mem_mapState_iff.1 hmem
    obtain ⟨u, ⟨s, hu, ha⟩, hru⟩ := hm
    refine (SeqCst.mem_read_iff ℓ t a).2 ⟨s.mem, ha.symm, ?_⟩
    refine Relation.ReflTransGen.trans ?_ hr
    have := SeqCst.refines_map (St.mem (Tid := Tid) (Loc := Loc) (Val := Val)) hru
    rwa [show u = [(s, s)] from hu] at this
  · intro hmem
    obtain ⟨μ, ha, hr⟩ := (SeqCst.mem_read_iff ℓ t a).1 hmem
    refine SeqCst.mem_mapState_iff.2
      ⟨[((⟨μ, fun _ ↦ []⟩ : St Tid Loc Val), (⟨μ, fun _ ↦ []⟩ : St Tid Loc Val))], ?_, hr⟩
    exact ha ▸ mem_readSC ℓ ⟨μ, fun _ ↦ []⟩

/-- **Buffering is invisible to the sequentially consistent view.**  Issuing a TSO
write abstracts to a stutter, so it lies below `pure` — it changes nothing an
abstract observer of memory can see. -/
theorem toSeqCst_writeCore_le [DecidableEq Tid] (i : Tid) (ℓ : Loc) (v : Val) :
    toSeqCst (writeCore i ℓ v) ≤ (pure PUnit.unit : SeqCst.Comp Loc Val PUnit) := by
  refine Brookes.le_of_mem fun t a hmem ↦ ?_
  obtain ⟨t₀, hm, hr⟩ := SeqCst.mem_mapState_iff.1 hmem
  obtain ⟨u, ⟨s, hu⟩, hru⟩ := hm
  refine (Brookes.mem_pure_iff PUnit.unit a t).2 ⟨rfl, ?_⟩
  have hmap := SeqCst.refines_map (St.mem (Tid := Tid) (Loc := Loc) (Val := Val)) hru
  rw [show u = [(s, s.push i ℓ v)] from hu] at hmap
  have hstut : (SeqCst.rewriting (SeqCst.Store Loc Val)).Refines []
      (List.map (Prod.map St.mem St.mem) [(s, s.push i ℓ v)]) :=
    Relation.ReflTransGen.single (SeqCst.Step.stutter s.mem [])
  exact (hstut.trans hmap).trans hr

/-- The abstraction is nevertheless not degenerate: as long as the write really
changes memory somewhere, a buffered write and a sequentially consistent write
stay different even after forgetting buffers. -/
theorem toSeqCst_writeCore_ne_writeSC [DecidableEq Tid] [DecidableEq Loc]
    (i : Tid) (ℓ : Loc) (v : Val) {μ : Loc → Val} (hμ : Function.update μ ℓ v ≠ μ) :
    toSeqCst (writeCore i ℓ v) ≠ toSeqCst (Tid := Tid) (writeSC ℓ v) := by
  intro heq
  have hle : SeqCst.write (Loc := Loc) (Val := Val) ℓ v ≤ pure PUnit.unit := by
    rw [← toSeqCst_writeSC (Tid := Tid) ℓ v, ← heq]
    exact toSeqCst_writeCore_le i ℓ v
  have hmem := hle (SeqCst.mem_write ℓ v μ)
  obtain ⟨-, h0⟩ := (Brookes.mem_pure_iff PUnit.unit PUnit.unit _).1 hmem
  exact hμ (SeqCst.compat_eq_of_refines_nil h0 (μ, Function.update μ ℓ v) (by simp)).symm

end TSO

end Isotope.Elgot.Brookes
