#import "../../syntax.typ": *
#import "../../todos.typ": *

#import "../rules/haslb.typ": *

#show: show-syntax

#definition[
  #todo-inline[
    an SSA model over an expression space $ms("E")$ and terminator space $ms("T")$
    --  Note that the previous section means one of these is _generated_ for every model over a
    function space $ms("F")$
  ]
]

#todo[Note that #cond-calc() is a sublanguage of #gssa-calc()]

#todo[#ssa-calc() is a sublanguage of #gssa-calc()]

#dntty($haslb(Γ, r, ms("L"))$, $cal(C)(Π ⟦Γ⟧, Σ ⟦ms("L")⟧)$)

#eqn-astack(
  dntdef(r-g-assign, $clet(⟦hasty(Γ, e, A)⟧) cc α^⊗ cc ⟦haslb(#$Γ, x : A$, r, ms("L"))⟧$),
  dntdef(r-g-br, todo-inline("this")),
  dntdef(r-g-case, todo-inline("this")),
  dntdef(r-g-scope, todo-inline("this")),
)

#dntty($klbrs(cal(K), L, ms("L"))$, $cal(C)(Σ ⟦Γ csplat K⟧, Σ ⟦ms("L")⟧)$)

#todo[General $cal(K)$-rules...]

#eqn-astack(
  dntdef(r-g-lb-nil, todo-inline("this")),
  dntdef(r-g-lb-cons, todo-inline("this")),
)

#lemma(name: "Weakening")[
  For all derivations $D : deriv(haslb(Γ, r, ms("K"))) $, $D' : deriv(haslb(Δ, r, ms("L")))$,
  if $cwk(Γ, Δ)$ and $lbcwk(ms("L"), ms("K"))$, we have that
  $⟦D⟧ = ⟦cwk(Γ, Δ)⟧ cc ⟦D'⟧ cc ⟦lbcwk(ms("L"), ms("K"))⟧$.

  In particular, if $Γ = Δ$ and $ms("L") = ms("K")$, then $⟦D⟧ = ⟦D'⟧$.
]

#lemma(name: "Soundness (Effect)")[
  If $ehaslb(Γ, ε, a, ms("L"))$, then $⟦haslb(Γ, a, ms("L"))⟧ : cal(C)_ε (Π ⟦Γ⟧, Σ ⟦ms("L")⟧)$
]

#lemma(name: "Soundness (Substitution)")[
  #todo-inline[this]
]

#theorem(name: "Soundness (Equivalence)")[
  Given $lbeq(Γ, req, s, t, ms("L"))$ and $cal(M) ⊧ req$, we have
  $
    ⟦haslb(Γ, s, ms("L"))⟧_cal(M) ->> ⟦haslb(Γ, t, ms("L"))⟧_cal(M)
  $
]

#theorem(name: "Completeness (Equivalence)")[
  Given $haslb(Γ, s, ms("L"))$ and $hasty(Γ, t, ms("L"))$, we have
  $
    lbeq(Γ, req, s, t, ms("L"))
    <==> (∀ cal(M) ⊧ req . haslb(Γ, s, A)⟧_cal(M) = ⟦haslb(Γ, t, A)⟧_cal(M))
  $
]


#definition[
  #todo-inline[
    a $cal(V)$-enriched SSA model over a function space $ms("F")$
    w/ _linear_ effect system $cal(E)$
  ]
]

#lemma(name: "Soundness (Directed Substitution)")[
  #todo-inline[this]
]


#definition[
  #todo-inline[
    a $cal(V)$-enriched SSA model modeling a refinement theory $rref$
  ]
]

#theorem(name: "Soundness (Refinement)")[
  Given $lbref(Γ, rref, s, t, ms("L"))$ and $cal(M) ⊧ rref$, we have
  $
    ⟦haslb(Γ, s, ms("L"))⟧_cal(M) ->> ⟦haslb(Γ, t, ms("L"))⟧_cal(M)
  $
]

#theorem(name: "Completeness (Refinement)")[
  Given $haslb(Γ, s, ms("L"))$ and $haslb(Γ, t, ms("L"))$, we have
  $
    tyref(Γ, rref, a, b, A)
    <==> (∀ cal(M) ⊧ rref . ⟦haslb(Γ, s, ms("L"))⟧_cal(M) ->> ⟦hasty(Γ, t, ms("L"))⟧_cal(M))
  $
]
