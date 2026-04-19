// One-stop import for all shared libraries.
// Usage: #import "/lib/prelude.typ": *

#import "/lib/thesis-template/mod.typ": appendix, thesis

#import "@preview/curryst:0.6.0": rule, prooftree, rule-set

#let chapter-quote(
  body,
  attribution: none,
) = [
  #quote(body, attribution: attribution, block: true)
]

#let ms(body) = $sans(body)$
#let mc(body) = $cal(body)$
#let mt(body) = $mono(body)$
#let mb(body) = $bold(body)$

// Default sets
#let vars = $N$
#let ops = $O$
#let types = $cal(T)$

// Grammars
#let sexp(ops, vars: none) = $ms("SExp")_vars (ops)$
#let ctx(types, vars: none) = $ms("Ctx")_vars (types)$

#let stty(inputs, op, outputs) = $op : inputs -> outputs$

#let hasty(ctx, exp, ty) = $ctx ⊢ exp : ty$