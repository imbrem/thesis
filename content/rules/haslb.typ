#import "../../syntax.typ": *


// Rules for gssa-calc(E, T)
#let r-g-assign = rule(
  name: "assign",
  $hasty(Γ, e, A)$,
  $haslb(#$Γ, x : A$, r, ms("L"))$,
  $haslb(#$Γ$, slet(x, e, r), ms("L"))$,
)
#let r-g-destruct = rule(
  name: [$"assign"_n$],
  $hasty(Γ, e, Π lb("T"))$,
  $haslb(#$Γ, lb("T")^V$, r, ms("L"))$,
  $haslb(#$Γ$, slet((V), e, r), ms("L"))$,
);
#let r-g-br = rule(
  name: "br",
  $lbcwk(lty(lb("l"), A), ms("L"))$,
  $hasty(Γ, e, A)$,
  $haslb(Γ, brb(lb("l"), e), ms("L"))$,
)
#let r-g-case = rule(
  name: "case",
  $hasty(Γ, e, Σ lb("L"))$,
  $ksbrs(Γ csplat lb("L"), L, ms("K"))$,
  $haslb(Γ, scase(e, L), ms("K"))$,
)
#let r-g-tm = rule(
  name: "tm",
  $haslb(Γ, τ, ms("L"), annot: ms("T"))$,
  $haslb(Γ, τ, ms("L"))$,
);
#let r-g-scope = rule(
  name: "scope",
  $haslb(Γ, r, #$ms("L"), ms("K")$)$,
  $klbrs(Γ csplat ms("K"), L, #$ms("L"), ms("K")$)$,
  $haslb(Γ, #${r} ; L$, ms("L"))$,
)
#let r-g-lb-nil = rule(
  name: "lb-nil",
  $klbrs(cal(K), ·, ·)$,
)
#let r-g-lb-cons = rule(
  name: "lb-cons",
  $ksbrs(cal("K"), L, ms("L"))$,
  $haslb(#$Γ, x : A$, r, ms("L"))$,
  $klbrs(#$cal("K"), clty(lb("k"), Γ, A)$, #$L, sbr(lb("k"), x, r)$, ms("L"))$,
)

#let fig-haslb-gssa = figure(
  [
    #rule-set(
      declare-rule(r-g-assign),
      declare-rule(r-g-destruct),
      declare-rule(r-g-br),
      declare-rule(r-g-case),
      declare-rule(r-g-tm),
      declare-rule(r-g-scope),
      declare-rule(r-g-lb-nil),
      declare-rule(r-g-lb-cons),
    )
    \
  ],
  caption: [Typing rules for #gssa-calc(ms("E"), ms("T"))],
)

#fig-haslb-gssa
