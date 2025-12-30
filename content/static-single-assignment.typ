#import "../syntax.typ": *
#import "../todos.typ": *

#context if (thesis-state.get)().is-standalone {
  set document(title: "Static Single Assignment (SSA)")
  title()
}

#show : show-syntax

= From RTL to SSA

#todo[still need a note about $(V)$]

#todo[
  when I say indexed family, I mean
  - a family over $I$. only ordered if $I$ is canonically ordered
  - in particular, lists are actually pairs $(n ↦ a)$ with standard order on $n ∈ ℕ$
]

#todo[
  If we manage to prove lattice substitution, remove label-set annotations
]

#import "rules/intro.typ": *

#todo[RTL text]

#rtl-flat-grammar <rtl-grammar>

#todo[text]

#rtl-10-fact

#todo[text]

#todo[convert factorial to SSA]

#rtl-flat-grammar <bba-grammar>

= Lexical SSA

#todo[text]

#todo[convert factorial to lexical SSA]

#lex-ssa-op-grammar <lex-ssa-op-grammar>

= Expressions and Substitution

#todo[text]

#iter-calc-grammar <iter-calc-grammar>

#lex-ssa-grammar <lex-ssa-grammar>

= Type-Theoretic SSA

#todo[text]

#tt-ssa-grammar <tt-ssa-grammar>