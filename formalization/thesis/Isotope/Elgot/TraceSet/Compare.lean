import Isotope.Elgot.Trace
import Isotope.Elgot.TraceSet.Laws

/-!
# Comparing `FiniteTrace` with `TraceSet`

The deterministic finite-trace model `FiniteTrace Sigma` of `Isotope.Elgot.Trace`
embeds into the nondeterministic trace sets over the free monoid `FreeMonoid Sigma`:
a terminating computation becomes a singleton, divergence becomes `∅`.

The embedding preserves `pure`, `bind` **and** `iter` on the nose.  Iteration is
preserved exactly because *both* models discard the traces of productive infinite
loops; against a model that retained them the statement would only be an
inclusion.
-/

namespace Isotope.Elgot

universe u

variable {Sigma Tau A B : Type u} [MulAction (FreeMonoid Sigma) Tau]

/-- Embed a deterministic finite-trace computation as a trace set: termination
becomes the singleton of its trace, divergence becomes the empty set. -/
def FiniteTrace.toTraceSet (x : FiniteTrace Sigma A) : TraceSet (FreeMonoid Sigma) Tau A :=
  ⟨{u | ∃ p : A × FreeMonoid Sigma, p ∈ x ∧ u = Trace.done p.1 p.2}⟩

namespace FiniteTrace

omit [MulAction (FreeMonoid Sigma) Tau] in
@[simp] theorem mem_toTraceSet_iff (x : FiniteTrace Sigma A)
    (u : Trace (FreeMonoid Sigma) Tau A) :
    u ∈ (x.toTraceSet : TraceSet (FreeMonoid Sigma) Tau A) ↔
      ∃ a w, (a, w) ∈ x ∧ u = Trace.done a w := by
  constructor
  · rintro ⟨⟨a, w⟩, hp, rfl⟩
    exact ⟨a, w, hp, rfl⟩
  · rintro ⟨a, w, hp, rfl⟩
    exact ⟨(a, w), hp, rfl⟩

omit [MulAction (FreeMonoid Sigma) Tau] in
@[simp] theorem inf_not_mem_toTraceSet (x : FiniteTrace Sigma A) (t : Tau) :
    Trace.inf t ∉ (x.toTraceSet : TraceSet (FreeMonoid Sigma) Tau A) := by
  intro hu
  rcases (mem_toTraceSet_iff x _).1 hu with ⟨a, w, _, heq⟩
  exact absurd heq (by simp)

omit [MulAction (FreeMonoid Sigma) Tau] in
@[simp] theorem toTraceSet_done (w : FreeMonoid Sigma) (a : A) :
    ((done w a).toTraceSet : TraceSet (FreeMonoid Sigma) Tau A) = {Trace.done a w} := by
  apply TraceSet.ext
  intro u
  rw [mem_toTraceSet_iff, TraceSet.mem_singleton_iff]
  constructor
  · rintro ⟨a', w', hp, rfl⟩
    rw [mem_done_iff] at hp
    cases hp
    rfl
  · rintro rfl
    exact ⟨a, w, (mem_done_iff _ _ _).2 rfl, rfl⟩

omit [MulAction (FreeMonoid Sigma) Tau] in
@[simp] theorem toTraceSet_diverge :
    ((diverge : FiniteTrace Sigma A).toTraceSet : TraceSet (FreeMonoid Sigma) Tau A) = ∅ := by
  apply TraceSet.ext
  intro u
  constructor
  · intro hu
    rcases (mem_toTraceSet_iff _ _).1 hu with ⟨a, w, hp, _⟩
    exact (not_mem_diverge (a, w) hp).elim
  · intro hu
    exact hu.elim

@[simp] theorem toTraceSet_pure (a : A) :
    ((pure a : FiniteTrace Sigma A).toTraceSet : TraceSet (FreeMonoid Sigma) Tau A) = pure a := by
  apply TraceSet.ext
  intro u
  rw [mem_toTraceSet_iff, TraceSet.mem_pure_iff]
  constructor
  · rintro ⟨a', w, hp, rfl⟩
    rw [mem_pure_iff] at hp
    cases hp
    rfl
  · rintro rfl
    exact ⟨a, 1, (mem_pure_iff a _).2 rfl, rfl⟩

@[simp] theorem toTraceSet_bind (x : FiniteTrace Sigma A) (f : A → FiniteTrace Sigma B) :
    ((x >>= f).toTraceSet : TraceSet (FreeMonoid Sigma) Tau B)
      = (x.toTraceSet >>= fun a ↦ (f a).toTraceSet) := by
  apply TraceSet.ext
  intro u
  rw [mem_toTraceSet_iff]
  constructor
  · rintro ⟨b, w, hp, rfl⟩
    rw [mem_bind_iff] at hp
    rcases hp with ⟨a, head, tail, ha, hb, rfl⟩
    refine (TraceSet.mem_bind_iff' _ _ _).2 ⟨Trace.done a head, ?_, ?_⟩
    · exact (mem_toTraceSet_iff _ _).2 ⟨a, head, ha, rfl⟩
    · rw [TraceSet.bindTrace_done]
      exact TraceSet.mem_smul.2
        ⟨Trace.done b tail, (mem_toTraceSet_iff _ _).2 ⟨b, tail, hb, rfl⟩, rfl⟩
  · intro hu
    rcases (TraceSet.mem_bind_iff' _ _ _).1 hu with ⟨v, hv, hw⟩
    rcases (mem_toTraceSet_iff _ _).1 hv with ⟨a, head, ha, rfl⟩
    rw [TraceSet.bindTrace_done] at hw
    rcases TraceSet.mem_smul.1 hw with ⟨w', hw', rfl⟩
    rcases (mem_toTraceSet_iff _ _).1 hw' with ⟨b, tail, hb, rfl⟩
    exact ⟨b, head * tail,
      (mem_bind_iff x f b (head * tail)).2 ⟨a, head, tail, ha, hb, rfl⟩, rfl⟩

omit [MulAction (FreeMonoid Sigma) Tau] in
theorem toTraceSet_injective :
    Function.Injective (toTraceSet (Sigma := Sigma) (Tau := Tau) (A := A)) := by
  intro x y h
  apply FiniteTrace.ext
  apply _root_.Part.ext
  rintro ⟨a, w⟩
  have hx : (Trace.done a w : Trace (FreeMonoid Sigma) Tau A) ∈
        (x.toTraceSet : TraceSet (FreeMonoid Sigma) Tau A) ↔
      (Trace.done a w : Trace (FreeMonoid Sigma) Tau A) ∈
        (y.toTraceSet : TraceSet (FreeMonoid Sigma) Tau A) := by rw [h]
  rw [mem_toTraceSet_iff, mem_toTraceSet_iff] at hx
  constructor
  · intro hp
    rcases hx.1 ⟨a, w, hp, rfl⟩ with ⟨a', w', hp', heq⟩
    cases heq
    exact hp'
  · intro hp
    rcases hx.2 ⟨a, w, hp, rfl⟩ with ⟨a', w', hp', heq⟩
    cases heq
    exact hp'

omit [MulAction (FreeMonoid Sigma) Tau] in
/-- The image of the embedding is deterministic: at most one trace. -/
theorem toTraceSet_subsingleton (x : FiniteTrace Sigma A)
    (u v : Trace (FreeMonoid Sigma) Tau A) (hu : u ∈ x.toTraceSet) (hv : v ∈ x.toTraceSet) :
    u = v := by
  rcases (mem_toTraceSet_iff _ _).1 hu with ⟨a, w, hp, rfl⟩
  rcases (mem_toTraceSet_iff _ _).1 hv with ⟨a', w', hp', rfl⟩
  have h1 : (a, w) ∈ x.toPart := hp
  have h2 : (a', w') ∈ x.toPart := hp'
  cases _root_.Part.mem_unique h1 h2
  rfl

theorem runs_toTraceSet_iff (f : A → FiniteTrace Sigma (B ⊕ A)) (a : A)
    (u : Trace (FreeMonoid Sigma) Tau B) :
    TraceSet.Runs
        (fun a ↦ ((f a).toTraceSet : TraceSet (FreeMonoid Sigma) Tau (B ⊕ A))) a u ↔
      ∃ b w, u = Trace.done b w ∧ Runs f a b w := by
  constructor
  · intro hr
    induction hr with
    | @ret a b e hs =>
        rcases (mem_toTraceSet_iff _ _).1 hs with ⟨s, w, hp, heq⟩
        cases heq
        exact ⟨b, _, rfl, Runs.done hp⟩
    | @div a t hs => exact absurd hs (by simp)
    | @more a a' e u' hs _ ih =>
        rcases (mem_toTraceSet_iff _ _).1 hs with ⟨s, w, hp, heq⟩
        cases heq
        rcases ih with ⟨b, w', rfl, hr'⟩
        exact ⟨b, _, rfl, Runs.more hp hr'⟩
  · rintro ⟨b, w, rfl, hr⟩
    induction hr with
    | done hs => exact TraceSet.Runs.ret ((mem_toTraceSet_iff _ _).2 ⟨_, _, hs, rfl⟩)
    | more hs _ ih => exact TraceSet.Runs.more ((mem_toTraceSet_iff _ _).2 ⟨_, _, hs, rfl⟩) ih

/-- The embedding commutes with iteration on the nose: both models discard the
traces of productive infinite loops. -/
theorem toTraceSet_iter (f : A → FiniteTrace Sigma (B ⊕ A)) (a : A) :
    ((iter f a).toTraceSet : TraceSet (FreeMonoid Sigma) Tau B)
      = iter (fun a ↦ ((f a).toTraceSet : TraceSet (FreeMonoid Sigma) Tau (B ⊕ A))) a := by
  apply TraceSet.ext
  intro u
  rw [mem_toTraceSet_iff]
  constructor
  · rintro ⟨b, w, hp, rfl⟩
    rw [mem_iter_iff] at hp
    exact (runs_toTraceSet_iff f a _).2 ⟨b, w, rfl, hp⟩
  · intro hu
    rcases (runs_toTraceSet_iff f a u).1 hu with ⟨b, w, rfl, hr⟩
    exact ⟨b, w, (mem_iter_iff f a b w).2 hr, rfl⟩

end FiniteTrace

end Isotope.Elgot
