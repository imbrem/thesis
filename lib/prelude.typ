// One-stop import for all shared libraries.
// Usage: #import "/lib/prelude.typ": *

#import "/lib/thesis-template/mod.typ": appendix, thesis
#import "/lib/template.typ": part, chapter, thesis-info

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

#let seq = $\; med$
#let lexp(x, a, e) = $ms("let") med #x = #a seq #e$

#let rwopt(lhs, rhs) = $
  #lhs
  quad quad --> quad quad
  #rhs                         
$

#let rwbad(lhs, rhs) = $
  #lhs
  quad quad cancel(-->) quad quad
  #rhs
$

// Default sets
#let vars = $N$
#let ops = $O$
#let vals = $V$
#let types = $cal(T)$

// Grammars
#let sexp1(ops, vars: none) = $ms("STm")_vars (ops)$
#let csexp1(ops) = $ms("STm")_∅ (ops)$

#let ctx(types, vars: none) = $ms("Ctx")_vars (types)$

#let stty(inputs, op, outputs) = $op : inputs -> outputs$

#import "/lib/todos.typ": todo

#let hasty(ctx, exp, ty) = $ctx ⊢ exp : ty$

#let sadd = $+$
#let smul = $·$
#let sneg = $-$
#let sdiv = $slash$


#let fv(sexp) = $sans("use")(sexp)$
#let ecv(ectx) = $sans("def")(ectx)$

#let evop(func) = $sans("ev")(func)$
#let stev(expr) = $sans("ev")(expr)$
#let ssto = $→$
#let pto = $⇀$
#let bsto = $⇓$
#let sred = $attach(->, tr: *)$

#let rfn = $→$
#let eqv = $≈$

#let red-seq(..args) = {
  let parts = args.pos()
  let result = parts.first()
  for part in parts.slice(1) {
    result = $#result --> #part$
  }
  $
  #result
  $
}

// TODO: fix this
#let def-set(..defs) = {
  let parts = defs.pos()
  let result = parts.first()
  for part in parts.slice(1) {
    result = $#result #h(4em) #part$
  }
  $
  result
  $
}

#let sexp(..args) = {
  let parts = args.pos()
  let result = parts.first()
  for part in parts.slice(1) {
    result = $#result med #part$
  }
  $(#result)$
}

#let lang-name(name) = $λ_ms(#name)$

#let larith = lang-name("arith");
#let lexpr = lang-name("expr");
#let lop = lang-name("op");
#let lbb = lang-name("bb");
#let lareg = lang-name("areg");
#let lreg = lang-name("reg");