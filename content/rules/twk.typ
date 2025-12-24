#import "../../syntax.typ": *

#let r-twk-base = rule(
  name: "base",
  $X sle(ms("X")) Y$,
  $tywk(tybase(X), tybase(Y))$,
);
#let r-twk-sigma = rule(
  name: $Σ$,
  $tywk(Σ lb("T"), Σ lb("T"'))$,
  $tywk(A, A')$,
  $tywk(Σ (lb("T"), lty(lb("f"), A)), Σ (lb("T")', lty(lb("f"), A')))$,
);
#let r-twk-pi = rule(
  name: $Π$,
  $tywk(Π lb("T"), Π lb("T"'))$,
  $tywk(A, A')$,
  $tywk(Π (lb("T"), fty(lb("f"), A)), Π (lb("T")', fty(lb("f"), A')))$,
);
#let r-twk-zero = rule(
  name: $tzero$,
  $tywk(tzero, A)$,
);
#let r-twk-unit = rule(
  name: $tunit$,
  $tywk(A, tunit)$,
);

#let r-ctxwk-nil = rule(
  name: "Π-nil",
  $cwk(Γ, ·)$,
)
#let r-ctxwk-cons = rule(
  name: "Π-cons",
  $clbwk(Γ, Δ)$,
  $tywk(A, B)$,
  $cwk(#$Γ, x : A$, #$Δ, x : A$)$,
);

#let r-lbwk-nil = rule(
  name: "Σ-nil",
  $lbcwk(·, ms("K"))$,
)
#let r-lbwk-cons = rule(
  name: "Σ-cons",
  $lbcwk(ms("L"), ms("K"))$,
  $tywk(A, B)$,
  $cwk(#$ms("L"), lb("l")(A)$, #$ms("K"), lb("l")(B)$)$,
);

#let r-clwk-nil = rule(
  name: "ΣΠ-nil",
  $clbwk(·, cal("K"))$,
)
#let r-clwk-cons = rule(
  name: "ΣΠ-cons",
  $clbwk(cal("L"), cal("K"))$,
  $cwk(Γ, Δ)$,
  $tywk(A, B)$,
  $clbwk(#$cal("L"), clty(lb("l"), Γ, A)$, #$cal("K"), clty(lb("l"), Δ, B)$)$,
);

#let r-isaff-base = rule(
  name: "base",
  $isaff(ms("U"), X)$,
  $isaff(ms("U"), tybase(X))$
);
#let r-isaff-sigma = rule(
  name: $Σ$,
  $∀ lb("l")(A) ∈ lb("L") . isaff(ms("U"), A)$,
  $isaff(ms("U"), Σ lb("L"))$,
);
#let r-isaff-pi = rule(
  name: $Π$,
  $∀ lb("l")(A) ∈ lb("L") . isaff(ms("U"), A)$,
  $isaff(ms("U"), Π lb("L"))$,
);

#let r-isrel-base = rule(
  name: "base",
  $isrel(ms("U"), X)$,
  $isrel(ms("U"), tybase(X))$
);
#let r-isrel-sigma = rule(
  name: $Σ$,
  $∀ lb("l")(A) ∈ lb("L") . isrel(ms("U"), A)$,
  $isrel(ms("U"), Σ lb("L"))$,
);
#let r-isrel-pi = rule(
  name: $Π$,
  $∀ lb("l")(A) ∈ lb("L") . isrel(ms("U"), A)$,
  $isrel(ms("U"), Π lb("L"))$,
);

#let r-utywk-base = rule(
  name: "base",
  $X sle(ms("U")) Y$,
  $utywk(ms("U"), tybase(X), tybase(Y))$,
)
#let r-utywk-sigma = rule(
  name: $Σ$,
  $utywk(ms("U"), Σ lb("T"), Σ lb("T"'))$,
  $utywk(ms("U"), A, A')$,
  $utywk(ms("U"), Σ (lb("T"), lty(lb("f"), A)), Σ (lb("T")', lty(lb("f"), A')))$,
);
#let r-utywk-pi = rule(
  name: $Π$,
  $utywk(ms("U"), Π lb("T"), Π lb("T"'))$,
  $utywk(ms("U"), A, A')$,
  $utywk(ms("U"), Π (lb("T"), fty(lb("f"), A,)), Π (lb("T")', fty(lb("f"), A')))$,
);
#let r-utywk-zero = rule(
  name: $tzero$,
  $utywk(ms("U"), tzero, A)$,
);
#let r-utywk-unit = rule(
  name: [$tunit$-base],
  $isaff(ms("U"), X)$,
  $utywk(ms("U"), tybase(X), tunit)$,
);