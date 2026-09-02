import Isotope.Elgot.Brookes.TSO.Invariant
import Mathlib.Tactic.Set

/-!
# Store buffering: TSO admits it, sequential consistency forbids it

The classic litmus test.  Two threads run

    thread 1:  x := 1 ; r₁ := y            thread 2:  y := 1 ; r₂ := x

from a state in which `x = y = 0`.  Sequential consistency forbids the outcome
`r₁ = r₂ = 0`; TSO admits it, because each write may sit in its thread's store
buffer while the other thread reads.

Both programs are written in the *same* monad, `TSO.Comp`, over the same
store-buffer state: the only difference is whether a write updates memory in one
step (`writeSC`) or is buffered and later committed (`write`).  So the separation
below is a genuine comparison of trace sets, not a translation between models.

The impossibility argument is the usual cycle
`W₁ < R₁ < W₂ < R₂ < W₁`, mechanised through the `Wrote`/`Reads` invariant of
`TSO/Invariant.lean`: each thread's trace satisfies `Wrote`, which pins the read
after the write, and the four auxiliary lemmas below propagate the monotonicity
of memory (`v0` can become `v1`, never the reverse) along the interleaving.
-/

namespace Isotope.Elgot.Brookes

universe u

namespace TSO

variable {Tid Loc Val : Type u} [DecidableEq Loc] {x y : Loc} {v0 v1 : Val}

/-! ## The four propagation lemmas -/

/-- If the location thread 1 is waiting to read already holds `v1`, and thread 2
never writes anything else there, thread 1 cannot read `v0`. -/
theorem reads_absurd (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Tid Loc Val}
    (hi : Interleave t₁ t₂ t) :
    ∀ {s sf : St Tid Loc Val}, Seq s t sf → Reads x v1 y v0 t₁ → OkAll y v1 t₂ →
      s.mem y = v1 → False := by
  induction hi with
  | nil => intro s sf _ h₁ _ _; cases h₁
  | @left e t₁' t₂' w _ ih =>
    intro s sf hs h₁ h₂ hy
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₁ with
      | here hp hr _ => exact hv (hr.symm.trans ((hp.mem_ne (Ne.symm hxy)).trans hy))
      | there hp h₁' => exact ih hs' h₁' h₂ ((hp.mem_ne (Ne.symm hxy)).trans hy)
  | @right e t₁' t₂' w _ ih =>
    intro s sf hs h₁ h₂ hy
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' => exact ih hs' h₁ h₂.tail (h₂.head.keeps hy)

/-- The mirror image of `reads_absurd`, with the two threads exchanged. -/
theorem reads_absurd' (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Tid Loc Val}
    (hi : Interleave t₁ t₂ t) {s sf : St Tid Loc Val} (hs : Seq s t sf)
    (h₁ : OkAll x v1 t₁) (h₂ : Reads y v1 x v0 t₂) (hx : s.mem x = v1) : False :=
  reads_absurd (Ne.symm hxy) hv hi.swap hs h₂ h₁ hx

/-- If the location thread 2 will read already holds `v1`, thread 2's pending
`write`-then-`read` cannot complete with the value `v0`. -/
theorem wrote_absurd (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Tid Loc Val}
    (hi : Interleave t₁ t₂ t) :
    ∀ {s sf : St Tid Loc Val}, Seq s t sf → OkAll x v1 t₁ → Wrote y v1 x v0 t₂ →
      s.mem x = v1 → False := by
  induction hi with
  | nil => intro s sf _ _ h₂ _; cases h₂
  | @left e t₁' t₂' w _ ih =>
    intro s sf hs h₁ h₂ hx
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' => exact ih hs' h₁.tail h₂ (h₁.head.keeps hx)
  | @right e t₁' t₂' w hi' ih =>
    intro s sf hs h₁ h₂ hx
    cases h₂ with
    | write _ _ hreads => exact reads_absurd' hxy hv (Interleave.right hi') hs h₁ hreads hx
    | skip hp h₂' =>
      obtain ⟨q, q'⟩ := e
      cases hs with
      | cons hs' => exact ih hs' h₁ h₂' ((hp.mem_ne hxy).trans hx)

/-- Thread 1 is about to read `v0` from `y`, thread 2 still owes its write to `y`
and its read of `x`, and `x` already holds `v1`: impossible. -/
theorem reads_wrote_absurd (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Tid Loc Val}
    (hi : Interleave t₁ t₂ t) :
    ∀ {s sf : St Tid Loc Val}, Seq s t sf → Reads x v1 y v0 t₁ → Wrote y v1 x v0 t₂ →
      s.mem y = v0 → s.mem x = v1 → False := by
  induction hi with
  | nil => intro s sf _ h₁ _ _ _; cases h₁
  | @left e t₁' t₂' w hi' ih =>
    intro s sf hs h₁ h₂ hy hx
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₁ with
      | here hp _ hall => exact wrote_absurd hxy hv hi' hs' hall h₂ (hp.keeps hx)
      | there hp h₁' =>
        exact ih hs' h₁' h₂ ((hp.mem_ne (Ne.symm hxy)).trans hy) (hp.keeps hx)
  | @right e t₁' t₂' w hi' ih =>
    intro s sf hs h₁ h₂ hy hx
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₂ with
      | write _ hset hreads =>
        exact reads_absurd hxy hv hi' hs' h₁ hreads.okAll.tail hset
      | skip hp h₂' =>
        rcases hp with hmem | hmem
        · exact ih hs' h₁ h₂' (by rw [show q'.mem = s.mem from hmem]; exact hy)
            (by rw [show q'.mem = s.mem from hmem]; exact hx)
        · refine reads_absurd hxy hv hi' hs' h₁ h₂'.okAll ?_
          rw [show q'.mem = Function.update s.mem y v1 from hmem]
          exact Function.update_self _ _ _

/-- **Store buffering is impossible for two `Wrote` threads.**  If each thread
puts `v1` into memory at its own location *before* observing the other's, and
both observe `v0`, the two orderings contradict. -/
theorem store_buffering_absurd (hxy : x ≠ y) (hv : v0 ≠ v1) {t₁ t₂ t : Tr Tid Loc Val}
    (hi : Interleave t₁ t₂ t) :
    ∀ {s sf : St Tid Loc Val}, Seq s t sf → Wrote x v1 y v0 t₁ → Wrote y v1 x v0 t₂ →
      s.mem x = v0 → s.mem y = v0 → False := by
  induction hi with
  | nil => intro s sf _ h₁ _ _ _; cases h₁
  | @left e t₁' t₂' w hi' ih =>
    intro s sf hs h₁ h₂ hx hy
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₁ with
      | write hp hset hreads =>
        cases hreads with
        | here _ _ hall => exact wrote_absurd hxy hv hi' hs' hall h₂ hset
        | there _ hreads' =>
          exact reads_wrote_absurd hxy hv hi' hs' hreads' h₂
            ((hp.mem_ne (Ne.symm hxy)).trans hy) hset
      | skip hp h₁' =>
        rcases hp with hmem | hmem
        · exact ih hs' h₁' h₂ (by rw [show q'.mem = s.mem from hmem]; exact hx)
            (by rw [show q'.mem = s.mem from hmem]; exact hy)
        · refine wrote_absurd hxy hv hi' hs' h₁'.okAll h₂ ?_
          rw [show q'.mem = Function.update s.mem x v1 from hmem]
          exact Function.update_self _ _ _
  | @right e t₁' t₂' w hi' ih =>
    intro s sf hs h₁ h₂ hx hy
    obtain ⟨q, q'⟩ := e
    cases hs with
    | cons hs' =>
      cases h₂ with
      | write hp hset hreads =>
        cases hreads with
        | here _ _ hall =>
          exact wrote_absurd (Ne.symm hxy) hv hi'.swap hs' hall h₁ hset
        | there _ hreads' =>
          exact reads_wrote_absurd (Ne.symm hxy) hv hi'.swap hs' hreads' h₁
            ((hp.mem_ne hxy).trans hx) hset
      | skip hp h₂' =>
        rcases hp with hmem | hmem
        · exact ih hs' h₁ h₂' (by rw [show q'.mem = s.mem from hmem]; exact hx)
            (by rw [show q'.mem = s.mem from hmem]; exact hy)
        · refine wrote_absurd (Ne.symm hxy) hv hi'.swap hs' h₂'.okAll h₁ ?_
          rw [show q'.mem = Function.update s.mem y v1 from hmem]
          exact Function.update_self _ _ _

/-! ## The two programs -/

/-- The store-buffering thread under sequential consistency: write `v` to `wl`,
then read `rl`. -/
def sbSC (wl rl : Loc) (v : Val) : Comp Tid Loc Val Val :=
  writeSC wl v >>= fun _ ↦ readSC rl

/-- Every execution of the sequentially consistent thread writes to memory before
it reads.  This is the whole content of "sequential consistency" here, and it
holds of the *closed* trace set because `Wrote` survives stuttering and
mumbling. -/
theorem sbSC_wrote {wl rl : Loc} (hk : rl ≠ wl) {t : Tr Tid Loc Val} {r : Val}
    (h : (t, r) ∈ sbSC wl rl v1) : Wrote wl v1 rl r t := by
  obtain ⟨a, u, v, hu, hv, hr⟩ := (Brookes.mem_bind_iff _ _ _ _).1 h
  obtain ⟨u₀, hu₀, hu'⟩ := hu
  obtain ⟨μ, hμ⟩ := hu₀
  obtain ⟨v₀, hv₀, hv'⟩ := hv
  obtain ⟨ρ, hρ, hrv⟩ := hv₀
  have hraw : Wrote wl v1 rl r ([(μ, μ.setMem wl v1)] ++ [(ρ, ρ)]) :=
    .write (Or.inr rfl) (Function.update_self _ _ _)
      (.there (Or.inr rfl) (.here (okStep_stutter _ _ _) hrv.symm (okAll_nil _ _)))
  refine Wrote.refines hk ((Rewriting.refines_append ?_ ?_).trans hr) hraw
  · exact hμ ▸ hu'
  · exact hρ ▸ hv'

/-- **Sequential consistency forbids store buffering.**  No interference-free
execution of the two sequentially consistent threads, started from a state in
which both locations hold `v0`, has both threads read `v0`. -/
theorem sc_forbids_store_buffering (hxy : x ≠ y) (hv : v0 ≠ v1)
    {s sf : St Tid Loc Val} (hx : s.mem x = v0) (hy : s.mem y = v0)
    {t : Tr Tid Loc Val} (hseq : Seq s t sf) :
    (t, (v0, v0)) ∉ par (sbSC x y v1) (sbSC y x v1) := by
  intro hmem
  obtain ⟨w₀, t₁, t₂, h₁, h₂, hi, hr⟩ := mem_par_iff.1 hmem
  exact store_buffering_absurd hxy hv hi (Seq.of_refines hr hseq)
    (sbSC_wrote (Ne.symm hxy) h₁) (sbSC_wrote hxy h₂) hx hy

section TSOWitness

variable [DecidableEq Tid]

/-- The store-buffering thread under TSO: buffer `wl := v`, then read `rl`. -/
def sbTSO (i : Tid) (wl rl : Loc) (v : Val) : Comp Tid Loc Val Val :=
  write i wl v >>= fun _ ↦ read i rl

/-- The initial state of the litmus test: every location holds `v0` and every
write buffer is empty. -/
def initSt (v0 : Val) : St Tid Loc Val := ⟨fun _ ↦ v0, fun _ ↦ []⟩

/-- **TSO admits store buffering.**  There is an interference-free execution of
the two TSO threads from the all-`v0` state in which both read `v0`: each thread
buffers its write, both read before either buffer drains, and the buffers drain
afterwards. -/
theorem tso_admits_store_buffering {i j : Tid} (hij : i ≠ j) (hxy : x ≠ y) :
    ∃ (t : Tr Tid Loc Val) (sf : St Tid Loc Val),
      (t, (v0, v0)) ∈ par (sbTSO i x y v1) (sbTSO j y x v1) ∧ Seq (initSt v0) t sf := by
  set s0 : St Tid Loc Val := initSt v0 with hs0
  set s1 : St Tid Loc Val := s0.push i x v1 with hs1
  set s2 : St Tid Loc Val := s1.push j y v1 with hs2
  set s3 : St Tid Loc Val :=
    ⟨Function.update s2.mem x v1, Function.update s2.buf i []⟩ with hs3
  set s4 : St Tid Loc Val :=
    ⟨Function.update s3.mem y v1, Function.update s3.buf j []⟩ with hs4
  have hbi : s2.buf i = [(x, v1)] := by
    simp [hs2, hs1, hs0, initSt, St.push, Function.update_of_ne hij]
  have hbj : s2.buf j = [(y, v1)] := by
    simp [hs2, hs1, hs0, initSt, St.push, Function.update_of_ne (Ne.symm hij)]
  have hbj3 : s3.buf j = [(y, v1)] := by
    rw [hs3]; simpa [Function.update_of_ne (Ne.symm hij)] using hbj
  have hm2 : s2.mem = fun _ ↦ v0 := by simp [hs2, hs1, hs0, initSt, St.push]
  have hoi : s2.observe i y = v0 := by
    simp [St.observe, hbi, Buf.peek, hxy, hm2]
  have hoj : s2.observe j x = v0 := by
    simp [St.observe, hbj, Buf.peek, Ne.symm hxy, hm2]
  have hfi : FlushRel i s2 s3 := ⟨x, v1, [], hbi, by rw [hs3]⟩
  have hfj : FlushRel j s3 s4 := ⟨y, v1, [], hbj3, by rw [hs4]⟩
  have hti : FlushTrace i [(s2, s3)] := by
    intro p hp; rw [List.mem_singleton.1 hp]; exact hfi
  have htj : FlushTrace j [(s3, s4)] := by
    intro p hp; rw [List.mem_singleton.1 hp]; exact hfj
  have hri : (([(s2, s2)] : Tr Tid Loc Val), v0) ∈ readCore i y := hoi ▸ mem_readCore i y s2
  have hrj : (([(s2, s2)] : Tr Tid Loc Val), v0) ∈ readCore j x := hoj ▸ mem_readCore j x s2
  have hwi : (([(s0, s1)] : Tr Tid Loc Val), PUnit.unit) ∈ write i x v1 :=
    Brookes.mem_bind _ _ (nil_mem_pflush i PUnit.unit)
      (Brookes.mem_bind _ _ (mem_writeCore i x v1 s0 PUnit.unit) (nil_mem_pflush i PUnit.unit))
  have hwj : (([(s1, s2)] : Tr Tid Loc Val), PUnit.unit) ∈ write j y v1 :=
    Brookes.mem_bind _ _ (nil_mem_pflush j PUnit.unit)
      (Brookes.mem_bind _ _ (mem_writeCore j y v1 s1 PUnit.unit) (nil_mem_pflush j PUnit.unit))
  have hrdi : (([(s2, s2), (s2, s3)] : Tr Tid Loc Val), v0) ∈ read i y :=
    Brookes.mem_bind _ _ (nil_mem_pflush i PUnit.unit)
      (Brookes.mem_bind _ _ hri
        (Brookes.mem_bind _ _ (mem_pflush hti PUnit.unit) (Brookes.mem_pure v0)))
  have hrdj : (([(s2, s2), (s3, s4)] : Tr Tid Loc Val), v0) ∈ read j x :=
    Brookes.mem_bind _ _ (nil_mem_pflush j PUnit.unit)
      (Brookes.mem_bind _ _ hrj
        (Brookes.mem_bind _ _ (mem_pflush htj PUnit.unit) (Brookes.mem_pure v0)))
  have h₁ : (([(s0, s1), (s2, s2), (s2, s3)] : Tr Tid Loc Val), v0) ∈ sbTSO i x y v1 :=
    Brookes.mem_bind _ _ hwi hrdi
  have h₂ : (([(s1, s2), (s2, s2), (s3, s4)] : Tr Tid Loc Val), v0) ∈ sbTSO j y x v1 :=
    Brookes.mem_bind _ _ hwj hrdj
  refine ⟨[(s0, s1), (s1, s2), (s2, s2), (s2, s2), (s2, s3), (s3, s4)], s4, ?_, ?_⟩
  · exact mem_par h₁ h₂ (.left (.right (.left (.right (.left (.right .nil))))))
  · exact .cons (.cons (.cons (.cons (.cons (.cons .nil)))))

/-- **TSO is strictly richer than sequential consistency.**  The store-buffering
outcome is realised by an interference-free TSO execution and by no
interference-free sequentially consistent one. -/
theorem tso_strictly_richer {i j : Tid} (hij : i ≠ j) (hxy : x ≠ y) (hv : v0 ≠ v1) :
    (∃ (t : Tr Tid Loc Val) (sf : St Tid Loc Val),
        (t, (v0, v0)) ∈ par (sbTSO i x y v1) (sbTSO j y x v1) ∧
          Seq (initSt v0) t sf) ∧
      ∀ (t : Tr Tid Loc Val) (sf : St Tid Loc Val), Seq (initSt v0) t sf →
        (t, (v0, v0)) ∉ par (sbSC x y v1) (sbSC y x v1) :=
  ⟨tso_admits_store_buffering hij hxy,
   fun _ _ hseq ↦ sc_forbids_store_buffering hxy hv rfl rfl hseq⟩

end TSOWitness

end TSO

end Isotope.Elgot.Brookes
