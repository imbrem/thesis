#import "../../syntax.typ": *

#let r-twk-base = rule(
  name: "base",
  // $X, Y ∈ ms("X")$,
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

#let r-twk-unit = rule(
  name: $tunit$,
  $tywk(A, tunit)$,
);

#let r-twk-zero = rule(
  name: $tzero$,
  $tywk(tzero, A)$,
);