import Isotope.Elgot.Transformer.Writer.Divergence
import Mathlib.Data.Stream.Init

/-!
# The productive infinite-output writer: interface and obstruction

`Isotope.Elgot.Transformer.Writer.Divergence` shows that no `WriterT W m` retains the output of a
divergent loop.  A *productive* writer — one that delivers the infinite log `w₁ · w₂ · ⋯` of a
nonterminating run — therefore needs

1. a carrier for infinite output, `Winf`, with an ω-indexed product `streamProd`, and
2. a different **computation** carrier, since `WriterT W m A = m (A × W)` has no summand in which
   an infinite log could live.

This file supplies (1) as a typeclass interface and proves the sharp statement that separates it
from (2): the infinite product of a constant stream is a *left fixed point* of `w`, which exists in
`Winf` but provably never in `W` itself.

## Honest boundary

The productive writer **is not constructed here**, and no `Iterate`/`LawfulElgotMonad` instance is
declared for any infinite-output writer.  This is a scope decision with reasons, not a stalled
proof:

* It is not a transformer of `WriterT`.  The right carrier is a *trace* monad `m ((A × W) ⊕ Winf)`,
  which duplicates the (absent) `Isotope.Elgot.Trace` development and belongs with it.
* Codiagonality on that carrier needs a **block law** relating `streamProd` of a stream of blocks
  to `streamProd` of the stream of block products.  That law does not follow from
  `StreamMulAction`: a tail-invariant `streamProd` (a density predicate on `Stream' W`) satisfies
  `streamProd_cons` while refuting codiagonality.  We do not formalise that countermodel here,
  because it is stated about trace-set iteration, which does not exist on this branch.
* Producing the infinite branch at all requires corecursive construction of the effect stream from
  a non-termination witness, hence dependent choice.

What *is* proved here: the interface is consistent (`instStreamMulActionPUnit`), it forces the
fixed-point equation `streamProd (const w) = w • streamProd (const w)` (`streamProd_const`), and
consequently `Winf = W` is impossible whenever `W` is length-graded and `w` has positive length
(`no_streamProd_self`).  That is exactly the reason the carrier has to change.
-/

namespace Isotope.Elgot.Transformer.Writer

universe u

/-- A carrier for infinite output: an ω-indexed product of finite outputs. -/
class StreamProd (W : Type u) (Winf : Type u) where
  /-- The product of an infinite stream of finite outputs. -/
  streamProd : Stream' W → Winf

export StreamProd (streamProd)

/-- The structure a productive writer needs on its output: finite output acts on infinite output
by prefixing, and the ω-product is compatible with that action. -/
class StreamMulAction (W : Type u) (Winf : Type u) [Monoid W] extends
    MulAction W Winf, StreamProd W Winf where
  /-- Prefixing a stream by one finite output prefixes its product. -/
  streamProd_cons (a : W) (σ : Stream' W) : streamProd (Stream'.cons a σ) = a • streamProd σ

/-- The interface is consistent: the terminal completion satisfies every axiom.  It is of course
uninformative — it identifies all infinite behaviours — which is why it is recorded as a
consistency witness and nothing more. -/
instance instStreamMulActionPUnit (W : Type u) [Monoid W] :
    StreamMulAction W PUnit.{u + 1} where
  smul _ _ := PUnit.unit
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  streamProd _ := PUnit.unit
  streamProd_cons _ _ := rfl

variable {W Winf : Type u} [Monoid W]

/-- **The fixed-point equation of a productive loop.**  The infinite output of the loop that emits
`w` forever is absorbed by `w`. -/
theorem streamProd_const [StreamMulAction W Winf] (w : W) :
    streamProd (Winf := Winf) (Stream'.const w)
      = w • streamProd (Winf := Winf) (Stream'.const w) := by
  conv_lhs => rw [Stream'.const_eq w]
  exact StreamMulAction.streamProd_cons w (Stream'.const w)

/-- **The infinite output cannot live in `W`.**  If the completion were `W` itself, with `W`
acting on itself by multiplication, the previous theorem would exhibit a left fixed point of `w`;
a length-graded monoid has none.  So a productive writer over such a `W` must genuinely enlarge
the output carrier — and, by `Isotope.Elgot.Transformer.Writer.Divergence`, must also enlarge the
computation carrier, since `WriterT` has nowhere to put the enlarged output. -/
theorem no_streamProd_self (sp : Stream' W → W)
    (hcons : ∀ (a : W) (σ : Stream' W), sp (Stream'.cons a σ) = a * sp σ)
    (len : W → ℕ) (hlen : ∀ a b : W, len (a * b) = len a + len b)
    (w : W) (hw : 0 < len w) : False := by
  have h : sp (Stream'.const w) = w * sp (Stream'.const w) := by
    conv_lhs => rw [Stream'.const_eq w]
    exact hcons w (Stream'.const w)
  exact no_left_fixed len hlen w hw _ h.symm

end Isotope.Elgot.Transformer.Writer
