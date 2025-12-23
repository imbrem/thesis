#import "../../syntax.typ": *

// Rules for br-calc(E)
#let r-br = rule(
  name: "br",
  $lbwk(lty(lb("l"), A), ms("L"))$,
  $hasty(Γ, e, A)$,
  $haslb(Γ, brb(lb("l"), e), ms("L"))$,
);
#let r-case = rule(
  name: "case",
  $hasty(Γ, e, Σ lb("L"))$,
  $issbrs(Γ, lb("L"), K, ms("K"))$,
  $haslb(Γ, scase(e, K), ms("K"))$,
);
#let r-case-nil = rule(
  name: "case-nil",
  $issbrs(Γ, ·, ·, ·)$,
);
#let r-case-cons = rule(
  name: "case-cons",
  $issbrs(Γ, lb("L"), K, ms("K"))$,
  $haslb(#$Γ, x : A$, brb(lb("k"), e), ms("K"))$,
  $issbrs(Γ, #$lb("L"), lty(lb("l"), A)$, #$K, sbr(lb("l"), x, brb(lb("k"), e))$, ms("K"))$,
);

// Rules for ssa-calc(E, T)
#let r-assign = rule(
  name: "assign",
  $hasty(Γ, e, A)$,
  $haslb(#$Γ, x : A$, r, ms("L"))$,
  $haslb(#$Γ$, slet(x, e, r), ms("L"))$,
);
#let r-tm = rule(
  name: "tm",
  $haslb(Γ, τ, #$ms("L"), ms("K")$)$,
  $islbrs(Γ, ms("K"), L, #$ms("L"), ms("K")$)$,
  $haslb(Γ, #$τ ; L$, ms("L"))$,
);
#let r-lb-nil = rule(
  name: "lb-nil",
  $islbrs(Γ, ·, ·, ·)$,
);
#let r-lb-cons = rule(
  name: "lb-cons",
  $issbrs(Γ, ms("K"), L, ms("L"))$,
  $haslb(#$Γ, x : A$, r, ms("L"))$,
  $islbrs(Γ, #$ms("K"), lty(lb("k"), A)$, #$K, sbr(lb("k"), x, r)$, ms("L"))$,
);


// Rules for gssa-calc(E, T)
#let r-g-assign = rule(
  name: "assign",
  $hasty(Γ, e, A)$,
  $haslb(#$Γ, x : A$, r, ms("L"))$,
  $haslb(#$Γ$, slet(x, e, r), ms("L"))$,
)
#let r-g-br = rule(
  name: "br",
  $lbwk(lty(lb("l"), A), ms("L"))$,
  $hasty(Γ, e, A)$,
  $haslb(Γ, brb(lb("l"), e), ms("L"))$,
)
#let r-g-case = rule(
  name: "case",
  $hasty(Γ, e, Σ lb("L"))$,
  $issbrs(Γ, lb("L"), L, ms("K"))$,
  $haslb(Γ, scase(e, L), ms("K"))$,
)
#let r-g-scope = rule(
  name: "scope",
  $haslb(Γ, r, #$ms("L"), ms("K")$)$,
  $islbrs(Γ, ms("K"), L, #$ms("L"), ms("K")$)$,
  $haslb(Γ, #${r} ; L$, ms("L"))$,
)
#let r-g-lb-nil = rule(
  name: "lb-nil",
  $islbrs(Γ, ·, ·, ·)$,
)
#let r-g-lb-cons = rule(
  name: "lb-cons",
  $issbrs(Γ, ms("K"), L, ms("L"))$,
  $haslb(#$Γ, x : A$, r, ms("L"))$,
  $islbrs(Γ, #$ms("K"), lty(lb("k"), A)$, #$K, sbr(lb("k"), x, r)$, ms("L"))$,
)