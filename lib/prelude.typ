// One-stop import for all shared libraries.
// Usage: #import "/lib/prelude.typ": *

#import "/lib/thesis-template/mod.typ": appendix, thesis
#import "/lib/template.typ": part, chapter

#import "@preview/curryst:0.6.0": rule, prooftree, rule-set

#import "@preview/ctheorems:1.1.3": thmrules
#import "/lib/theorems.typ": theorem, lemma, corollary, definition, example, remark, proof


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
#let vals = $V$
#let types = $cal(T)$

// Grammars
#let sexp1(ops, vars: none) = $ms("STm")_vars (ops)$
#let ctx(types, vars: none) = $ms("Ctx")_vars (types)$

#let stty(inputs, op, outputs) = $op : inputs -> outputs$

#import "/lib/todos.typ": todo

#let hasty(ctx, exp, ty) = $ctx ⊢ exp : ty$

#let sexp(..args) = {
  let parts = args.pos()
  let result = parts.first()
  for part in parts.slice(1) {
    result = $#result med #part$
  }
  $(#result)$
}