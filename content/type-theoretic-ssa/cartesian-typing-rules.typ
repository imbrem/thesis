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

#def-cart-ty-sys

#todo[
  We define a type system $sty(ms("X"))$. 
  Where clear from context, we $tybase(·)$ transparently.
]

#fig-ty-grammar

#todo[We equip it with an order]

#fig-r-twk