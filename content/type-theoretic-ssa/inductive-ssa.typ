#import "../../syntax.typ": *
#import "../../todos.typ": *

#show: show-syntax

#context if (thesis-state.get)().is-standalone {
  set document(title: "Type-Theoretic SSA")
  title()
}

#todo[
  In this chapter we:
  1. Give a type-and-effect system for #iter-calc() and 
    SSA parametrized by a set of base types $ms("X")$
    - First we define a type system over types $ms("Ty")[ms("X")]$
    - Then we give typing rules for expressions and programs, _and_...
    - State some basic metatheory
  2. Give an _effect system_ for #iter-calc() and SSA
  2. Give a _refinement theory_ for #iter-calc() and SSA using our equational theory
    - Metatheory of refinement: weakening
]

= Types and Contexts

#import "../rules/types.typ": *

#todo[Everything is parametrized by a set of _base types_ $ms("X")$]

#def-ty-sys

#todo[
  For now, we assume a _cartesian_ type system
]

#todo[
  We define a type system $sty(ms("X"))$. 
  Where clear from context, we $tybase(·)$ transparently.
]

#fig-ty-grammar

#todo[We equip it with an order]

#fig-r-twk

#todo[
  This is in fact a near-prelattice; and hence induces a cartesian type system on $sty(ms("X"))$
]

#fig-r-cwk

#todo[
  Likewise for contexts
]

= Expressions

#todo[introduce concept of a function space]

#todo[fix notation for function space judgement]

#import "../rules/hasty.typ": *

#fig-r-hasty

#todo[explain #op-calc(ms("F")), #case-calc(ms("F")) as sublanguages of #iter-calc(ms("F"))]

#todo[weakening]

#todo[substitution]

= Regions

#todo[introduce concept of an _expression space_]

#todo[fix notation for expression space judgement]

#import "../rules/haslb.typ": *

#fig-haslb-br

#todo[introduce concept of a _region space_]

#fig-haslb-ssa

#todo[weakening]

#todo[substitution]

#todo[SSA is just a region-space too... hence gSSA]

#fig-haslb-gssa

#todo[weakening]

#todo[substitution]

#todo[label-substitution]

= Effects

#todo[want to build an equational theory]

#todo[substitution is not good equationally]

#todo[want a notion of _effects_]

#todo[introduce _effect systems_]

== Expressions

#todo[introduce _direct_ effects (versus indirect, up to equivalence)]

#fig-r-eff-hasty

== Regions

#todo[introduce _effect labels_ for SSA]

#todo[rules...]

= Refinement

#todo[in fact, want a _refinement theory_]

#todo[(expression) basis ; refinement system _over_ $ms("E")$ ; order]

#todo[basic metatheory]

#todo[(region) basis ; refinement system _over_ $ms("E") ; ms("T")$ ; order embedding]

#todo[basic metatheory]