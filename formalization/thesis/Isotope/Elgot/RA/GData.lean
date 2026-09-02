import Isotope.Elgot.RA.GTrace

/-!
# `𝔤`-rewrites in pointwise normal form

All three rules of the generating group act on a pre-trace `α ξ ω ◁ r` in the
same shape: the chronicle splits as a prefix `l` and a suffix `m.map f`, the
prefix is mapped by some `h`, each transition `f T` of the suffix is replaced
by `g T`, and both delimiting views are mapped by some `hv`.  For `Loosen` and
`Expel` the maps `h` and `hv` are the identity; for `Condense` they are the
pull along `ε` (journal §7.3, pp.30–33).

`GData` bundles that shape together with everything the surgery of Rewrite
Castling and of Proposition 7.5 needs:

* `mk_step` — *any* decomposition of the same shape is again a rewrite, which
  is what lets the surgery hand back a rewrite after re-partitioning the lists;
* `mk_trace` — the corresponding transfer lemma of
  `Isotope/Elgot/RA/GTrace.lean`;
* `hv_mono` — Lemma 7.6 for this rewrite, i.e. `hv` is monotone on views that
  point into the source's closing memory;
* `h_stutter`, `fg_stutter`, `h_mumble`, `fg_mumble` — the compatibility of the
  maps with the two `𝔠` rules that reshape the chronicle.

The bundle is **ours**; the paper works with the rules directly and organizes
the case analysis by Table 4's "'er/'ee" roles instead (journal p.61).
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {A : Type u}

/-! ## Two chain lemmas -/

/-- Deleting a transition whose opening memory is contained in its closing one
leaves an adjacent chronicle. -/
theorem isChain_remove_mid {P Q : List (Transition Loc Val)} {T : Transition Loc Val}
    (h : List.IsChain Adj (P ++ T :: Q)) (hT : T.opening ⊆ T.closing) :
    List.IsChain Adj (P ++ Q) := by
  obtain ⟨hP, hTQ, hlast⟩ := List.isChain_append.mp h
  obtain ⟨hhead, hQ⟩ := List.isChain_cons.mp hTQ
  refine List.isChain_append.2 ⟨hP, hQ, fun x hx y hy ↦ ?_⟩
  exact subset_trans (hlast x hx T (by simp)) (subset_trans hT (hhead y hy))

/-- Splitting a transition `⟨a,c⟩` into `⟨a,b⟩⟨b,c⟩` leaves an adjacent
chronicle. -/
theorem isChain_split_mid {P Q : List (Transition Loc Val)} {a b c : Memory Loc Val}
    (h : List.IsChain Adj (P ++ (⟨a, c⟩ : Transition Loc Val) :: Q)) :
    List.IsChain Adj (P ++ (⟨a, b⟩ : Transition Loc Val) :: ⟨b, c⟩ :: Q) := by
  obtain ⟨hP, hTQ, hlast⟩ := List.isChain_append.mp h
  obtain ⟨hhead, hQ⟩ := List.isChain_cons.mp hTQ
  refine List.isChain_append.2 ⟨hP, ?_, fun x hx y hy ↦ ?_⟩
  · exact List.isChain_cons_cons.2 ⟨subset_refl _, List.isChain_cons.2 ⟨hhead, hQ⟩⟩
  · rw [Option.mem_def, List.head?_cons, Option.some.injEq] at hy
    subst hy
    exact hlast x hx ⟨a, c⟩ (by simp)

/-! ## The bundle -/

/-- A `𝔤`-rewrite of the pre-trace `τ` whose target chronicle is `c'`.  The
target pre-trace is then `⟨hv τ.ivw, c', hv τ.fvw, τ.ret⟩`. -/
structure GData (R : RuleSet) (τ : PreTrace Loc Val A) (c' : Chro Loc Val) where
  /-- The action on the two delimiting views. -/
  hv : View Loc → View Loc
  /-- The action on the transitions of the prefix. -/
  h : Transition Loc Val → Transition Loc Val
  /-- The source shape of the transitions of the rewritten suffix. -/
  f : Transition Loc Val → Transition Loc Val
  /-- The target shape of the transitions of the rewritten suffix. -/
  g : Transition Loc Val → Transition Loc Val
  /-- The disjointness carried by the paper's `⊎`. -/
  free : Transition Loc Val → Prop
  /-- The prefix. -/
  l : List (Transition Loc Val)
  /-- The rewritten suffix, in source shape. -/
  m : List (Transition Loc Val)
  /-- Every transition of the suffix is free of the rewritten messages. -/
  hfree : ∀ T ∈ m, free T
  /-- The source chronicle. -/
  src : τ.ch.toList = l ++ m.map f
  /-- The target chronicle. -/
  tgt : c'.toList = l.map h ++ m.map g
  /-- Any decomposition of the same shape is again a rewrite. -/
  mk_step : ∀ (α ω : View Loc) (s : A) (d₁ d₂ : Chro Loc Val)
    (l' m' : List (Transition Loc Val)), (∀ T ∈ m', free T) →
    d₁.toList = l' ++ m'.map f → d₂.toList = l'.map h ++ m'.map g →
    Step R ⟨α, d₁, ω, s⟩ ⟨hv α, d₂, hv ω, s⟩
  /-- Any decomposition of the same shape takes traces to traces, given that
  the target's memories are well-formed. -/
  mk_trace : ∀ (α ω : View Loc) (s : A) (d₁ d₂ : Chro Loc Val)
    (l' m' : List (Transition Loc Val)), (∀ T ∈ m', free T) →
    d₁.toList = l' ++ m'.map f → d₂.toList = l'.map h ++ m'.map g →
    IsTrace ⟨α, d₁, ω, s⟩ → (∀ T ∈ d₂.toList, T.WF) → IsTrace ⟨hv α, d₂, hv ω, s⟩
  /-- Lemma 7.6 for this rewrite. -/
  hv_mono : ∀ κ σ : View Loc, PointsInto κ τ.ch.c → PointsInto σ τ.ch.c → κ ≤ σ →
    hv κ ≤ hv σ
  /-- The prefix action takes stutter transitions to stutter transitions. -/
  h_stutter : ∀ μ : Memory Loc Val, ∃ μ' : Memory Loc Val,
    h ⟨μ, μ⟩ = ⟨μ', μ'⟩
  /-- So does the suffix substitution. -/
  fg_stutter : ∀ S : Transition Loc Val, free S → ∀ μ : Memory Loc Val, f S = ⟨μ, μ⟩ →
    ∃ μ' : Memory Loc Val, g S = ⟨μ', μ'⟩
  /-- The prefix action commutes with splitting a transition in two. -/
  h_mumble : ∀ a b c : Memory Loc Val, a ⊆ b → b ⊆ c → WellFormed b →
    WellFormed (h ⟨a, c⟩).opening → WellFormed (h ⟨a, c⟩).closing →
    (h ⟨a, b⟩).opening = (h ⟨a, c⟩).opening ∧ (h ⟨b, c⟩).closing = (h ⟨a, c⟩).closing ∧
      (h ⟨a, b⟩).closing = (h ⟨b, c⟩).opening ∧ WellFormed (h ⟨a, b⟩).closing ∧
      (h ⟨a, c⟩).opening ⊆ (h ⟨a, b⟩).closing ∧ (h ⟨a, b⟩).closing ⊆ (h ⟨a, c⟩).closing
  /-- So does the suffix substitution: a transition of the suffix splits into
  two transitions of the suffix. -/
  fg_mumble : ∀ S : Transition Loc Val, free S → ∀ a b c : Memory Loc Val,
    f S = ⟨a, c⟩ → a ⊆ b → b ⊆ c → WellFormed b →
    WellFormed (g S).opening → WellFormed (g S).closing →
    ∃ S₁ S₂ : Transition Loc Val, free S₁ ∧ free S₂ ∧ f S₁ = ⟨a, b⟩ ∧ f S₂ = ⟨b, c⟩ ∧
      (g S₁).opening = (g S).opening ∧ (g S₂).closing = (g S).closing ∧
      (g S₁).closing = (g S₂).opening ∧ WellFormed (g S₁).closing ∧
      (g S).opening ⊆ (g S₁).closing ∧ (g S₁).closing ⊆ (g S).closing

/-! ## `Loosen` in normal form -/

/-- The `Loosen` rule as a `GData`. -/
def gDataLoosen {R : RuleSet} (hx : Rule.Ls ∈ R) {α ω : View Loc} {r : A}
    {c₁ c₂ : Chro Loc Val} {l m : List (Transition Loc Val)} {ν ε : Msg Loc Val}
    (hle : Msg.LeVw ν ε) (hfε : listFree ε m) (hfν : listFree ν m)
    (e₁ : c₁.toList = l ++ m.map (Transition.insertMsg ε))
    (e₂ : c₂.toList = l ++ m.map (Transition.insertMsg ν)) :
    GData R (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A) c₂ where
  hv := id
  h := id
  f := Transition.insertMsg ε
  g := Transition.insertMsg ν
  free := fun T ↦ (ε ∉ T.opening ∧ ε ∉ T.closing) ∧ (ν ∉ T.opening ∧ ν ∉ T.closing)
  l := l
  m := m
  hfree := fun T hT ↦ ⟨hfε T hT, hfν T hT⟩
  src := e₁
  tgt := by rw [e₂]; simp
  mk_step := fun _ _ _ d₁ d₂ l' m' hm he₁ he₂ ↦
    Step.chro hx (ChroStep.loosen d₁ d₂ l' m' ν ε hle (fun T hT ↦ (hm T hT).1)
      (fun T hT ↦ (hm T hT).2) he₁ (by simpa using he₂))
  mk_trace := fun _ _ _ _ _ l' m' hm he₁ he₂ hτ hwf ↦
    isTrace_loosen hle (fun T hT ↦ (hm T hT).1) (fun T hT ↦ (hm T hT).2) he₁
      (by simpa using he₂) hτ hwf
  hv_mono := fun _ _ _ _ h ↦ h
  h_stutter := fun μ ↦ ⟨μ, rfl⟩
  fg_stutter := by
    intro S hS μ hf
    refine ⟨insert ν S.opening, ?_⟩
    have ho : insert ε S.opening = μ := congrArg Transition.opening hf
    have hc : insert ε S.closing = μ := congrArg Transition.closing hf
    have : S.opening = S.closing := Set.insert_cancel (ho.trans hc.symm) hS.1.1 hS.1.2
    rw [Transition.insertMsg, this]
  h_mumble := fun a b c hab hbc hwfb _ _ ↦ ⟨rfl, rfl, rfl, hwfb, hab, hbc⟩
  fg_mumble := by
    intro S hS a b c hfS hab hbc hwfb hwfo hwfc
    have ha : insert ε S.opening = a := congrArg Transition.opening hfS
    have hc : insert ε S.closing = c := congrArg Transition.closing hfS
    have hεb : ε ∈ b := hab (ha ▸ Set.mem_insert _ _)
    have hb : insert ε (b \ {ε}) = b := Set.insert_diff_self hεb
    have hbS : b \ {ε} ⊆ S.closing := by
      rintro x ⟨hxb, hxne⟩
      rcases (hc ▸ hbc hxb : x ∈ insert ε S.closing) with rfl | hx
      · exact absurd rfl hxne
      · exact hx
    have hSb : S.opening ⊆ b \ {ε} := by
      intro x hx
      exact ⟨hab (ha ▸ Set.mem_insert_of_mem _ hx), fun hxe ↦ hS.1.1 (hxe ▸ hx)⟩
    refine ⟨⟨S.opening, b \ {ε}⟩, ⟨b \ {ε}, S.closing⟩,
      ⟨⟨hS.1.1, fun h ↦ h.2 rfl⟩, ⟨hS.2.1, fun h ↦ hS.2.2 (hbS h)⟩⟩,
      ⟨⟨fun h ↦ h.2 rfl, hS.1.2⟩, ⟨fun h ↦ hS.2.2 (hbS h), hS.2.2⟩⟩,
      ?_, ?_, rfl, rfl, rfl, ?_, Set.insert_subset_insert hSb, Set.insert_subset_insert hbS⟩
    · rw [Transition.insertMsg, ha, hb]
    · rw [Transition.insertMsg, hb, hc]
    · refine WellFormed.of_subset (Z := insert ν S.closing) hwfc
        (Set.insert_subset_insert hbS) ⟨ν, Set.mem_insert _ _⟩ ?_
      intro ϑ hϑ
      rcases hϑ with rfl | hϑ
      · exact (hwfo.pointsDownInto (Set.mem_insert _ _)).mono (Set.insert_subset_insert hSb)
      · exact PointsDownInto.subst_insert (X := b \ {ε})
          (by rw [hb]; exact hwfb.pointsDownInto hϑ.1) hle.lc_eq hle.t_eq hle.vw_le

/-! ## `Expel` in normal form -/

/-- The `Expel` rule as a `GData`. -/
def gDataExpel {R : RuleSet} (hx : Rule.Ex ∈ R) {α ω : View Loc} {r : A}
    {c₁ c₂ : Chro Loc Val} {l m : List (Transition Loc Val)} {ν ε : Msg Loc Val}
    (hdt : Msg.Dovetail ν ε) (hfs : listFree (ε.setI ν.i hdt.i_lt_t) m)
    (hfν : listFree ν m) (hfε : listFree ε m)
    (e₁ : c₁.toList = l ++ m.map (Transition.insertMsg (ε.setI ν.i hdt.i_lt_t)))
    (e₂ : c₂.toList = l ++ m.map (fun T ↦ (T.insertMsg ε).insertMsg ν)) :
    GData R (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A) c₂ where
  hv := id
  h := id
  f := Transition.insertMsg (ε.setI ν.i hdt.i_lt_t)
  g := fun T ↦ (T.insertMsg ε).insertMsg ν
  free := fun T ↦ ((ε.setI ν.i hdt.i_lt_t) ∉ T.opening ∧ (ε.setI ν.i hdt.i_lt_t) ∉ T.closing)
    ∧ (ν ∉ T.opening ∧ ν ∉ T.closing) ∧ (ε ∉ T.opening ∧ ε ∉ T.closing)
  l := l
  m := m
  hfree := fun T hT ↦ ⟨hfs T hT, hfν T hT, hfε T hT⟩
  src := e₁
  tgt := by rw [e₂]; simp
  mk_step := fun _ _ _ d₁ d₂ l' m' hm he₁ he₂ ↦
    Step.chro hx (ChroStep.expel d₁ d₂ l' m' ν ε hdt (fun T hT ↦ (hm T hT).1)
      (fun T hT ↦ (hm T hT).2.1) (fun T hT ↦ (hm T hT).2.2) he₁ (by simpa using he₂))
  mk_trace := fun _ _ _ _ _ l' m' hm he₁ he₂ hτ hwf ↦
    isTrace_expel hdt (fun T hT ↦ (hm T hT).1) (fun T hT ↦ (hm T hT).2.1)
      (fun T hT ↦ (hm T hT).2.2) he₁ (by simpa using he₂) hτ hwf
  hv_mono := fun _ _ _ _ h ↦ h
  h_stutter := fun μ ↦ ⟨μ, rfl⟩
  fg_stutter := by
    intro S hS μ hf
    refine ⟨insert ν (insert ε S.opening), ?_⟩
    have ho : insert (ε.setI ν.i hdt.i_lt_t) S.opening = μ := congrArg Transition.opening hf
    have hc : insert (ε.setI ν.i hdt.i_lt_t) S.closing = μ := congrArg Transition.closing hf
    have : S.opening = S.closing := Set.insert_cancel (ho.trans hc.symm) hS.1.1 hS.1.2
    simp only [Transition.insertMsg, this]
  h_mumble := fun a b c hab hbc hwfb _ _ ↦ ⟨rfl, rfl, rfl, hwfb, hab, hbc⟩
  fg_mumble := by
    intro S hS a b c hfS hab hbc hwfb hwfo hwfc
    set ε' := ε.setI ν.i hdt.i_lt_t with hε'
    have ha : insert ε' S.opening = a := congrArg Transition.opening hfS
    have hc : insert ε' S.closing = c := congrArg Transition.closing hfS
    have hεb : ε' ∈ b := hab (ha ▸ Set.mem_insert _ _)
    have hb : insert ε' (b \ {ε'}) = b := Set.insert_diff_self hεb
    have hbS : b \ {ε'} ⊆ S.closing := by
      rintro x ⟨hxb, hxne⟩
      rcases (hc ▸ hbc hxb : x ∈ insert ε' S.closing) with rfl | hx
      · exact absurd rfl hxne
      · exact hx
    have hSb : S.opening ⊆ b \ {ε'} := by
      intro x hx
      exact ⟨hab (ha ▸ Set.mem_insert_of_mem _ hx), fun hxe ↦ hS.1.1 (hxe ▸ hx)⟩
    refine ⟨⟨S.opening, b \ {ε'}⟩, ⟨b \ {ε'}, S.closing⟩,
      ⟨⟨hS.1.1, fun h ↦ h.2 rfl⟩, ⟨hS.2.1.1, fun h ↦ hS.2.1.2 (hbS h)⟩,
        ⟨hS.2.2.1, fun h ↦ hS.2.2.2 (hbS h)⟩⟩,
      ⟨⟨fun h ↦ h.2 rfl, hS.1.2⟩, ⟨fun h ↦ hS.2.1.2 (hbS h), hS.2.1.2⟩,
        ⟨fun h ↦ hS.2.2.2 (hbS h), hS.2.2.2⟩⟩,
      ?_, ?_, rfl, rfl, rfl, ?_,
      Set.insert_subset_insert (Set.insert_subset_insert hSb),
      Set.insert_subset_insert (Set.insert_subset_insert hbS)⟩
    · rw [Transition.insertMsg, ha, hb]
    · rw [Transition.insertMsg, hb, hc]
    · refine WellFormed.of_subset (Z := insert ν (insert ε S.closing)) hwfc
        (Set.insert_subset_insert (Set.insert_subset_insert hbS)) ⟨ν, Set.mem_insert _ _⟩ ?_
      intro ϑ hϑ
      have hmono : insert ν (insert ε S.opening) ⊆ insert ν (insert ε (b \ {ε'})) :=
        Set.insert_subset_insert (Set.insert_subset_insert hSb)
      rcases hϑ with rfl | hϑ
      · exact (hwfo.pointsDownInto (Set.mem_insert _ _)).mono hmono
      · rcases hϑ with rfl | hϑ
        · exact (hwfo.pointsDownInto (Set.mem_insert_of_mem _ (Set.mem_insert _ _))).mono hmono
        · refine PointsDownInto.mono ?_ (Set.subset_insert _ _)
          exact PointsDownInto.subst_insert (ν := ε) (ε := ε') (X := b \ {ε'})
            (by rw [hb]; exact hwfb.pointsDownInto hϑ.1) rfl rfl (le_refl _)

/-! ## `Condense` in normal form -/

/-- The `Condense` rule as a `GData`.  Unlike the other two it needs the
target's memories to be well-formed, because its `hv_mono` is Lemma 7.6. -/
noncomputable def gDataCondense {R : RuleSet} (hx : Rule.Cn ∈ R) {α ω : View Loc} {r : A}
    {c₁ c₂ : Chro Loc Val} {l m : List (Transition Loc Val)} {ν ε : Msg Loc Val}
    (hde : Msg.DovetailEq ν ε) (hfν : listFree ν m) (hfε : listFree ε m)
    (e₁ : c₁.toList = l ++ m.map (fun T ↦ (T.insertMsg ε).insertMsg ν))
    (e₂ : c₂.toList = (l ++ m.map (Transition.insertMsg ν)).map (Transition.pull ε))
    (hwf₂ : ∀ T ∈ c₂.toList, T.WF) :
    GData R (⟨α, c₁, ω, r⟩ : PreTrace Loc Val A) c₂ where
  hv := View.pull ε
  h := Transition.pull ε
  f := fun T ↦ (T.insertMsg ε).insertMsg ν
  g := fun T ↦ (T.insertMsg ν).pull ε
  free := fun T ↦ (ν ∉ T.opening ∧ ν ∉ T.closing) ∧ (ε ∉ T.opening ∧ ε ∉ T.closing)
  l := l
  m := m
  hfree := fun T hT ↦ ⟨hfν T hT, hfε T hT⟩
  src := e₁
  tgt := by rw [e₂, List.map_append, List.map_map]; rfl
  mk_step := fun _ _ _ d₁ d₂ l' m' hm he₁ he₂ ↦
    Step.condense hx l' m' ν ε hde (fun T hT ↦ (hm T hT).1) (fun T hT ↦ (hm T hT).2) he₁
      (by rw [he₂, List.map_append, List.map_map]; rfl)
  mk_trace := fun _ _ _ _ _ l' m' hm he₁ he₂ hτ hwf ↦
    isTrace_condense hde (fun T hT ↦ (hm T hT).1) (fun T hT ↦ (hm T hT).2) he₁
      (by rw [he₂, List.map_append, List.map_map]; rfl) hτ hwf
  hv_mono := fun _ _ hκ hσ hle ↦ condense_mono hde hfε e₁ e₂ hwf₂ hκ hσ hle
  h_stutter := fun μ ↦ ⟨Memory.pull ε μ, rfl⟩
  fg_stutter := by
    intro S hS μ hf
    refine ⟨Memory.pull ε (insert ν S.opening), ?_⟩
    have hνne : ν ≠ ε := fun hc ↦ by
      rw [hc] at hde; exact absurd hde.1.2.1 (ne_of_gt ε.i_lt_t)
    have ho : insert ν (insert ε S.opening) = μ := congrArg Transition.opening hf
    have hc : insert ν (insert ε S.closing) = μ := congrArg Transition.closing hf
    have h1 : insert ε S.opening = insert ε S.closing :=
      Set.insert_cancel (ho.trans hc.symm)
        (by simp only [Set.mem_insert_iff, not_or]; exact ⟨hνne, hS.1.1⟩)
        (by simp only [Set.mem_insert_iff, not_or]; exact ⟨hνne, hS.1.2⟩)
    have h2 : S.opening = S.closing := Set.insert_cancel h1 hS.2.1 hS.2.2
    simp only [Transition.pull, Transition.insertMsg, h2]
  h_mumble := by
    intro a b c hab hbc hwfb hwfa hwfc
    refine ⟨rfl, rfl, rfl, ?_, Memory.pull_mono hab, Memory.pull_mono hbc⟩
    have hsub : Memory.pull ε b ⊆ Memory.pull ε c := Memory.pull_mono hbc
    refine WellFormed.of_subset (Z := Memory.pull ε c) hwfc hsub
      (Set.Nonempty.mono (Memory.pull_mono hab) hwfa.nonempty) ?_
    rintro _ ⟨ϑ, hϑ, rfl⟩
    exact PointsDownInto.pull_all hwfb (hwfc.scattered.mono hsub) (hwfb.pointsDownInto hϑ)
  fg_mumble := by
    intro S hS a b c hfS hab hbc hwfb hwfo hwfc
    have hνne : ν ≠ ε := fun hcc ↦ by
      rw [hcc] at hde; exact absurd hde.1.2.1 (ne_of_gt ε.i_lt_t)
    have ha : insert ν (insert ε S.opening) = a := congrArg Transition.opening hfS
    have hc : insert ν (insert ε S.closing) = c := congrArg Transition.closing hfS
    have hνb : ν ∈ b := hab (ha ▸ Set.mem_insert _ _)
    have hεb : ε ∈ b := hab (ha ▸ Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    have hb : insert ν (insert ε ((b \ {ν}) \ {ε})) = b := by
      rw [Set.insert_diff_self (show ε ∈ b \ {ν} from ⟨hεb, hνne.symm⟩),
        Set.insert_diff_self hνb]
    have hbdiff : (b \ {ν}) \ {ε} ⊆ S.closing := by
      rintro x ⟨⟨hxb, hxν⟩, hxε⟩
      rcases (hc ▸ hbc hxb : x ∈ insert ν (insert ε S.closing)) with rfl | hx
      · exact absurd rfl hxν
      · rcases hx with rfl | hx
        · exact absurd rfl hxε
        · exact hx
    have hSdiff : S.opening ⊆ (b \ {ν}) \ {ε} := by
      intro x hx
      exact ⟨⟨hab (ha ▸ Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hx)),
        fun hxe ↦ hS.1.1 (hxe ▸ hx)⟩, fun hxe ↦ hS.2.1 (hxe ▸ hx)⟩
    have hbε : b \ {ε} = insert ν ((b \ {ν}) \ {ε}) := by
      conv_lhs => rw [← hb]
      rw [Set.insert_insert_diff hνne (by simp)]
    refine ⟨⟨S.opening, (b \ {ν}) \ {ε}⟩, ⟨(b \ {ν}) \ {ε}, S.closing⟩,
      ⟨⟨hS.1.1, fun h ↦ h.1.2 rfl⟩, ⟨hS.2.1, fun h ↦ h.2 rfl⟩⟩,
      ⟨⟨fun h ↦ h.1.2 rfl, hS.1.2⟩, ⟨fun h ↦ h.2 rfl, hS.2.2⟩⟩, ?_, ?_, rfl, rfl, rfl, ?_,
      Memory.pull_mono (Set.insert_subset_insert hSdiff),
      Memory.pull_mono (Set.insert_subset_insert hbdiff)⟩
    · simp only [Transition.insertMsg, ha, hb]
    · simp only [Transition.insertMsg, hb, hc]
    · have hsub : Memory.pull ε (insert ν ((b \ {ν}) \ {ε})) ⊆
          Memory.pull ε (insert ν S.closing) :=
        Memory.pull_mono (Set.insert_subset_insert hbdiff)
      refine WellFormed.of_subset (Z := Memory.pull ε (insert ν S.closing)) hwfc hsub
        (Set.Nonempty.mono (Memory.pull_mono (Set.insert_subset_insert hSdiff))
          hwfo.nonempty) ?_
      rintro _ ⟨ϑ, hϑ, rfl⟩
      have hϑb : ϑ ∈ b := by
        rcases hϑ with rfl | hϑ
        · exact hνb
        · exact hϑ.1.1
      have := PointsDownInto.pull (ε := ε) (μ := b) hwfb hwfc.scattered
        (by rw [hbε]; exact hsub) (fun _ ↦ ⟨ν, hνb, hde.1⟩) (hwfb.pointsDownInto hϑb)
      rw [hbε] at this
      exact this

/-! ## Every `𝔤`-rewrite is in normal form -/

/-- Extraction: a rewrite by a rule of `𝔤` whose target is a trace carries a
`GData`. -/
theorem exists_gData {R : RuleSet} (hR : R ⊆ gRules) {τ π : PreTrace Loc Val A}
    (h : Step R τ π) (hπ : IsTrace π) :
    ∃ (c' : Chro Loc Val) (D : GData R τ c'),
      π = ⟨D.hv τ.ivw, c', D.hv τ.fvw, τ.ret⟩ := by
  cases h with
  | chro hx hcs =>
      cases hcs with
      | stutter => exact absurd (hR hx) (by simp)
      | mumble => exact absurd (hR hx) (by simp)
      | loosen _ _ l m ν ε hle hfε hfν e₁ e₂ =>
          exact ⟨_, gDataLoosen hx hle hfε hfν e₁ e₂, rfl⟩
      | expel _ _ l m ν ε hdt hfs hfν hfε e₁ e₂ =>
          exact ⟨_, gDataExpel hx hdt hfs hfν hfε e₁ e₂, rfl⟩
  | forward hx _ => exact absurd (hR hx) (by simp)
  | rewind hx _ => exact absurd (hR hx) (by simp)
  | condense hx l m ν ε hde hfν hfε e₁ e₂ =>
      exact ⟨_, gDataCondense hx hde hfν hfε e₁ e₂ hπ.wf, rfl⟩

end Isotope.Elgot.RA
