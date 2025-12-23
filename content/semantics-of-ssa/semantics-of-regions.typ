#import "../../syntax.typ": *
#import "../../todos.typ": *

#import "../rules/haslb.typ": *

#show: show-syntax

#todo[
  Definition: an SSA model over an expression space $ms("E")$ and terminator space $ms("T")$
  --  Note that the previous section means one of these is _generated_ for every model over a
  function space $ms("F")$
]

#todo[Note that #br-calc() is a sublanguage of #gssa-calc()]

#todo[#ssa-calc() is a sublanguage of #gssa-calc()]

#todo[typing]

#eqn-astack(
  dntdef(r-g-assign, $clet(⟦hasty(Γ, e, A)⟧) ; α^⊗ ; ⟦haslb(#$Γ, x : A$, r, ms("L"))⟧$),
  dntdef(r-g-br, todo-inline("this")),
  dntdef(r-g-case, todo-inline("this")),
  dntdef(r-g-scope, todo-inline("this")),
)

#todo[typing]

#eqn-astack(
  dntdef(r-g-lb-nil, todo-inline("this")),
  dntdef(r-g-lb-cons, todo-inline("this")),
)

#theorem(name: "Weakening")[
  #todo[this]
]

#corollary(name: "Coherence")[
  #todo[this]
]

#theorem(name: "Soundness (Effect)")[
  #todo[this]
]

#theorem(name: "Soundness (Substitution)")[
  #todo[this]
]

#theorem(name: "Soundness (Equivalence)")[
  #todo[this]
]

#theorem(name: "Completeness (Equivalence)")[
  #todo[this]
]

#theorem(name: "Soundness (Refinement)")[
  #todo[this]
]

#theorem(name: "Completeness (Refinement)")[
  #todo[this]
]

