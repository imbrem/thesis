// Operational semantics for λ_iter: the machine's grammars and step rules, as
// reusable `#let` definitions. Import into the chapter; nothing here renders on
// its own.
//
//   #import "/thesis/type-theoretic-ssa/lambda-iter/operational.typ": *
//
// The semantics is small-step, substitution-based, and *model-relative*: it is
// parametrized by a model M = (S, ⟦-⟧_M) interpreting the base types and the
// instructions. A configuration ⟨s | a⟩ pairs an abstract state s ∈ S with a
// closed M-term a. Only the `op` rule touches the state; every other rule is a
// pure rewrite. Divergence is the absence of a terminating run -- the `iter`
// rule consumes a step per iteration, so a loop that never exits really does
// step forever.
//
// Machine-level notation (cfg, mstep, semm, obs, …) lives in
// `/lib/notation/lambda-iter-opsem.typ`; term notation (letx, casex, iterx, …)
// in `/lib/notation/lambda-iter.typ`. Both arrive via the prelude.

#import "/lib/prelude.typ": *

// ===========================================================================
//  Grammars
// ===========================================================================

// M-terms extend the λ_iter grammar with a constant c_u for every element u of
// every ⟦X⟧_M, so that a closed M-term can name the model's values. Values are
// the constructor forms; note there is NO value at the empty type, which is
// what makes `abort` unreachable rather than stuck.
#let os-value-grammar = grammar(
  production($v, w$, $c_u$, $()$, $(v, w)$, linl($v$), linr($v$)),
)

// Evaluation contexts fix a left-to-right, call-by-value order. `iter E {…}`
// evaluates the loop's initial value before the loop starts; the loop body is
// NOT an evaluation context, since it only runs once the state is a value.
#let os-ectx-grammar = grammar(
  production(
    $E$,
    ehole,
    $f med E$,
    letx($x$, $E$, $b$),
    letx($(x, y)$, $E$, $c$),
    linebreak(),
    $(E, b)$,
    $(v, E)$,
    linl($E$),
    linr($E$),
    linebreak(),
    casex($E$, $x$, $a$, $y$, $b$),
    labort($E$),
    iterx($E$, $x$, $b$),
  ),
)

// ===========================================================================
//  Small-step rules  ⟨s | a⟩ →_M ⟨s' | a'⟩
// ===========================================================================

// Congruence: step under an evaluation context.
#let os-ctx = rule(
  label: msc("ctx"),
  mstep(cfg($s$, $a$), cfg($s'$, $a'$)),
  mstep(cfg($s$, eplug($E$, $a$)), cfg($s'$, eplug($E$, $a'$))),
)

// The only rule that reads or writes the state: an instruction applied to a
// value runs the model's interpretation of that instruction.
#let os-op = rule(
  label: msc("op"),
  $semm(f) med (s, v) = (s', w)$,
  mstep(cfg($s$, $f med v$), cfg($s'$, $w$)),
)

// Binding: substitute the value for the bound variable.
#let os-let = rule(
  label: msc("let"),
  mstep(cfg($s$, letx($x$, $v$, $b$)), cfg($s$, subvar($v$, $x$, $b$))),
)
#let os-let-pair = rule(
  label: msc("let-pair"),
  mstep(
    cfg($s$, letx($(x, y)$, $(v, w)$, $c$)),
    cfg($s$, subvar($v$, $x$, subvar($w$, $y$, $c$))),
  ),
)

// Branching: select the branch named by the injection.
#let os-case-l = rule(
  label: msc("case-l"),
  mstep(
    cfg($s$, casex(linl($v$), $x$, $a$, $y$, $b$)),
    cfg($s$, subvar($v$, $x$, $a$)),
  ),
)
#let os-case-r = rule(
  label: msc("case-r"),
  mstep(
    cfg($s$, casex(linr($w$), $x$, $a$, $y$, $b$)),
    cfg($s$, subvar($w$, $y$, $b$)),
  ),
)

// Iteration: one unrolling per step. The body is run with the current state
// value substituted in, and its result is dispatched by a `case` -- exiting on
// ι_l and re-entering the loop on ι_r. This is exactly the shape of `iter-β`,
// which is why that equation is validated on the nose.
#let os-iter = rule(
  label: msc("iter"),
  mstep(
    cfg($s$, iterx($v$, $x$, $b$)),
    cfg($s$, casex(subvar($v$, $x$, $b$), $y$, $y$, $z$, iterx($z$, $x$, $b$))),
  ),
)

#let os-step-rules = (
  os-ctx, os-op, os-let, os-let-pair, os-case-l, os-case-r, os-iter,
)

// ===========================================================================
//  Metatheory of the machine
// ===========================================================================

// Preservation: stepping preserves the type (and the effect bound, since no
// rule introduces a new instruction occurrence).
#let os-preservation = rule(
  label: msc("preservation"),
  hasty($·$, $a$, $A$),
  mstep(cfg($s$, $a$), cfg($s'$, $a'$)),
  hasty($·$, $a'$, $A$),
)

// Progress: a well-typed closed configuration is either a value or steps.
// There is no third case: `abort` is never a redex, because there is no value
// at the empty type, so a well-typed `abort a` always has a reducible `a`.
#let os-progress = rule(
  label: msc("progress"),
  hasty($·$, $a$, $A$),
  [$a ∈ mvals(A)$, or $mstep(cfg(s, a), cfg(s', a'))$ for some $s'$, $a'$],
)

// Determinism: the machine is a partial function on configurations.
#let os-determinism = rule(
  label: msc("determinism"),
  mstep(cfg($s$, $a$), cfg($s_1$, $a_1$)),
  mstep(cfg($s$, $a$), cfg($s_2$, $a_2$)),
  $s_1 = s_2 and a_1 = a_2$,
)

#let os-metatheory-rules = (os-preservation, os-progress, os-determinism)
