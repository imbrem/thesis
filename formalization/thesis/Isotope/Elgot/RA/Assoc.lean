import Isotope.Elgot.RA.Generating
import Isotope.Elgot.RA.Castling
import Isotope.Elgot.RA.Categorical
import Isotope.Elgot.RA.Concrete

/-!
# The Concrete model is a monad

Dvir, Kammar and Lahav, journal §7.4, p.34:

> **Proposition 7.7.**  `C` is a monad.

stated there **without proof**.  Its only supporting argument anywhere in the
paper is Example 8.6 (p.41), which covers associativity and sketches it as:

> *Deferral of Closure* helps show the associativity law holds for both `C` and
> `A`. […] To show the associativity law for `C`, we specialize *Deferral of
> Closure* to `★ = 𝔠`, and restrict to `P ∈ C X`, `f : X → C Y`, `g : Y → C Z`,
> obtaining `(P >>=_C f) >>=_C g = ((P >>=_G f)𝔠 >>=_G g)𝔠 = ((P >>=_G f) >>=_G g)𝔠`
> and `P >>=_C (λr. f r >>=_C g) = (P >>=_G (λr. f r >>=_G g)𝔠)𝔠 = (P >>=_G (λr. f r >>=_G g))𝔠`.

The two rewritings the sketch performs are exactly what this file supplies:
that `>>=_G` absorbs the `𝔤`-closure (Proposition 7.5,
`Isotope/Elgot/RA/Generating.lean`) and that on a `𝔤`-closed set the `𝔤𝔠`-closure
*is* the `𝔠`-closure (Rewrite Castling, `Isotope/Elgot/RA/Castling.lean`).  With
those, associativity at `𝔤𝔠` reduces to associativity at `𝔠`, which
`Isotope/Elgot/RA/Monad.lean` already has.

Together with the two unit laws of `Isotope/Elgot/RA/Concrete.lean` this
completes Proposition 7.7 — and hence, via `Isotope/Elgot/RA/Iteration.lean`,
`LawfulElgotMonad` and the Kleisli Elgot and Elgot-Freyd structure of the
Concrete model.  **All of it is original work**: the paper proves none of it.
-/

universe u

namespace Isotope.Elgot.RA

variable {Loc Val : Type} {A B C : Type u}

/-! ## Shrinking the rule set of a closed set -/

/-- Closedness is antitone in the rule set. -/
theorem Closed.anti {R R' : RuleSet} (hR : R ⊆ R') {S : Set (PreTrace Loc Val A)}
    (h : Closed R' S) : Closed R S := fun τ hτ π hstep ↦ h τ hτ π (hstep.mono hR)

/-- A computation of the Concrete model is in particular `𝔤`-closed. -/
theorem Comp.gClosed (P : Comp gcRules Loc Val A) : Closed gRules P.traces :=
  Closed.anti gRules_subset_gcRules P.closed

/-- The `𝔠`-closure of a `𝔤`-closed set of traces is again `𝔤`-closed: by
Rewrite Castling it *is* the `𝔤𝔠`-closure. -/
theorem closed_gRules_closure_cRules {S : Set (PreTrace Loc Val A)} (hS : IsTraceSet S)
    (hg : Closed gRules S) : Closed gRules (closure cRules S) := by
  rw [← closure_gcRules_eq hS hg]
  exact Closed.anti gRules_subset_gcRules (closure_closed gcRules S)

/-! ## Associativity -/

namespace Concrete

/-- **Associativity for the Concrete model `C`** — the remaining law of the
paper's Proposition 7.7 (ESOP Proposition 6.6), which is stated without proof.

The proof is the paper's own sketch (Example 8.6, journal p.41) made precise:
`bindGen` of `𝔤`-closed sets is `𝔤`-closed (Proposition 7.5), so on all the
sets involved the `𝔤𝔠`-closure coincides with the `𝔠`-closure (Rewrite
Castling), and there deferral of closure at the seam is available.
**Original work.** -/
theorem associativity (P : Comp gcRules Loc Val A) (f : A → Comp gcRules Loc Val B)
    (g : B → Comp gcRules Loc Val C) : P >>= f >>= g = P >>= fun a ↦ f a >>= g := by
  apply Comp.ext
  set F : A → Set (PreTrace Loc Val B) := fun a ↦ (f a).traces with hFdef
  set G : B → Set (PreTrace Loc Val C) := fun b ↦ (g b).traces with hGdef
  have hFt : ∀ a, IsTraceSet (F a) := fun a ↦ (f a).isTrace
  have hGt : ∀ b, IsTraceSet (G b) := fun b ↦ (g b).isTrace
  have hFg : ∀ a, Closed gRules (F a) := fun a ↦ (f a).gClosed
  have hGg : ∀ b, Closed gRules (G b) := fun b ↦ (g b).gClosed
  have hXt : IsTraceSet (bindGen P.traces F) := bindGen_isTrace P.isTrace hFt
  have hXg : Closed gRules (bindGen P.traces F) :=
    bindGen_closed P.isTrace hFt P.gClosed hFg
  have hYt : ∀ a, IsTraceSet (bindGen (F a) G) := fun a ↦ bindGen_isTrace (hFt a) hGt
  have hYg : ∀ a, Closed gRules (bindGen (F a) G) :=
    fun a ↦ bindGen_closed (hFt a) hGt (hFg a) hGg
  have hCXt : IsTraceSet (closure cRules (bindGen P.traces F)) := hXt.closure
  have hCXg : Closed gRules (closure cRules (bindGen P.traces F)) :=
    closed_gRules_closure_cRules hXt hXg
  change closure gcRules (bindGen (closure gcRules (bindGen P.traces F)) G)
    = closure gcRules (bindGen P.traces (fun a ↦ closure gcRules (bindGen (F a) G)))
  -- the left-hand side
  have hlhs : closure gcRules (bindGen (closure gcRules (bindGen P.traces F)) G)
      = closure gcRules (bindGen (bindGen P.traces F) G) := by
    rw [closure_gcRules_eq hXt hXg,
      closure_gcRules_eq (bindGen_isTrace hCXt hGt) (bindGen_closed hCXt hGt hCXg hGg),
      closure_bindGen_closure_left (subset_refl cRules) hXt hGt,
      ← closure_gcRules_eq (bindGen_isTrace hXt hGt) (bindGen_closed hXt hGt hXg hGg)]
  -- the right-hand side
  have hrhs : closure gcRules (bindGen P.traces (fun a ↦ closure gcRules (bindGen (F a) G)))
      = closure gcRules (bindGen P.traces (fun a ↦ bindGen (F a) G)) := by
    have hpt : (fun a ↦ closure gcRules (bindGen (F a) G))
        = fun a ↦ closure cRules (bindGen (F a) G) := by
      funext a; exact closure_gcRules_eq (hYt a) (hYg a)
    have hCYt : ∀ a, IsTraceSet (closure cRules (bindGen (F a) G)) := fun a ↦ (hYt a).closure
    have hCYg : ∀ a, Closed gRules (closure cRules (bindGen (F a) G)) :=
      fun a ↦ closed_gRules_closure_cRules (hYt a) (hYg a)
    rw [hpt,
      closure_gcRules_eq (bindGen_isTrace P.isTrace hCYt)
        (bindGen_closed P.isTrace hCYt P.gClosed hCYg),
      closure_bindGen_closure_right (subset_refl cRules) P.isTrace hYt,
      ← closure_gcRules_eq (bindGen_isTrace P.isTrace hYt)
        (bindGen_closed P.isTrace hYt P.gClosed hYg)]
  rw [hlhs, hrhs, bindGen_assoc]

end Concrete

/-- **The Concrete model `C` is a monad** — the paper's Proposition 7.7
(journal §7.4, p.34; ESOP Proposition 6.6), stated there without proof.
**Original work.** -/
instance : LawfulMonad (Comp gcRules Loc Val) := LawfulMonad.mk'
  (id_map := fun x ↦ Concrete.bind_pure x)
  (pure_bind := fun a f ↦ Concrete.pure_bind a f)
  (bind_assoc := fun x f g ↦ Concrete.associativity x f g)

/-! ## Consequences -/

open CategoryTheory

/-- The Kleisli category of the Concrete model is an Elgot category.  The
iteration operator is ours, not the paper's — §4 of the paper is explicit that
`λRA` has no loops. -/
theorem nonempty_elgotCategory_concrete (Loc Val : Type) :
    Nonempty (ElgotCategory
      (Kleisli (Kleisli.Type.TM (Comp gcRules Loc Val : Type u → Type u)))) :=
  ⟨inferInstance⟩

/-- …and an Elgot Freyd category over the pure-map inclusion. -/
theorem nonempty_elgotFreydCategory_concrete (Loc Val : Type) :
    Nonempty (ElgotFreydCategory
      (Kleisli.Adjunction.toKleisli
        (Kleisli.Type.TM (Comp gcRules Loc Val : Type u → Type u)))) :=
  ⟨inferInstance⟩

end Isotope.Elgot.RA
