// Notation for the operational semantics of λ_iter.
//
// Kept separate from `/lib/notation/lambda-iter.typ` (the surface syntax and
// the equational/refinement judgements) so the machine-level notation --
// states, configurations, steps, observations, models -- can be restyled
// independently.

#import "/lib/notation/lambda-iter.typ": *

// --- Models ----------------------------------------------------------------

// A model M = (S, ⟦-⟧) of the signature: a set of states plus an
// interpretation of every base type and instruction.
#let model = $cal(M)$
// The state space of a model, and the metavariables ranging over it.
#let states = $sans("S")$
// Interpretation brackets, subscripted by the model: ⟦-⟧_M.
#let semm(x) = $lr(⟦ #x ⟧)_model$
// The set of M-values of type A -- the closed values of type A over M's
// constants, canonically in bijection with ⟦A⟧_M.
#let mvals(a) = $sans("Val")_model (#a)$
// An M-environment γ ∈ ⟦Γ⟧_M, and its action on a term (the closing
// substitution it induces).
#let envact(g, a) = $#g (#a)$

// --- Configurations and steps ----------------------------------------------

// A configuration ⟨s | a⟩: the state s paired with the M-term being evaluated.
#let cfg(s, a) = $lr(⟨ #s mid(|) #a ⟩)$
// One step of the machine, in the model M: c →_M c'.
#let mstep(c, d) = $#c attach(→, br: model) #d$
// Many steps: c →*_M c'.
#let msteps(c, d) = $#c attach(attach(→, tr: *), br: model) #d$
// n steps: c →^n_M c'.
#let mstepn(c, d, n) = $#c attach(attach(→, tr: #n), br: model) #d$
// Divergence of a configuration: c ⇑_M.
#let mdiv(c) = $#c attach(⇑, br: model)$
// The divergent outcome itself.
#let odiv = $⇑$

// --- Evaluation contexts ---------------------------------------------------

// The hole of an evaluation context, and the plugging operation E[a].
#let ehole = $[dot]$
#let eplug(e, a) = $#e [#a]$

// --- Observations ----------------------------------------------------------

// The basic observation of a ∈ Term in model M from state s and environment γ:
// either a terminal pair (s', v) or the divergent outcome ⇑.
#let obs(a) = $sans("obs")_model (#a)$
#let obsat(s, g, a) = $sans("obs")_model (#s, #g, #a)$
// The refined, trace observation: the (finite or infinite) sequence of states
// the machine passes through, together with its terminal result if any.
#let trobs(s, g, a) = $sans("tr")_model (#s, #g, #a)$

// Observational equivalence Γ ⊨ a ≃ b : A -- indistinguishable in every model,
// from every state and environment.
#let obseq(g, a, b, ty) = $#g ⊨ #a ≃ #b : #ty$
#let obsne(g, a, b, ty) = $#g ⊨ #a cancel(≃) #b : #ty$
// Trace-observational equivalence Γ ⊨_tr a ≃ b : A.
#let obseqtr(g, a, b, ty) = $#g attach(⊨, br: sans("tr")) #a ≃ #b : #ty$

// --- Handlers (the bridge to the denotational semantics) -------------------

// The handler induced by a model: interp_M takes an interaction tree to a
// state transformer.
#let interp(t) = $sans("interp")_model (#t)$
// The pure part of a model: the total function φ_f interpreting a pure
// instruction f, independent of the state.
#let purefn(f) = $phi.alt_#f$
