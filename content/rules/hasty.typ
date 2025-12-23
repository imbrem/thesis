#import "../../syntax.typ": *

#let r-var = rule(
  name: "var",
  $Γ med x = A$,
  $hasty(Γ, x, A)$,
);
#let r-coe = rule(
  name: "coe",
  $hasty(Γ, a, A)$,
  $tywk(A, A')$,
  $hasty(Γ, a, A')$,
);
#let r-app = rule(
  name: "app",
  $isfn(Γ, f, A, B)$,
  $hasty(Γ, a, A)$,
  $hasty(Γ, f med a, B)$,
);
#let r-inj = rule(
  name: "inj",
  $hasty(Γ, a, A)$,
  $hasty(Γ, lb("l") med a, Σ (lty(lb("l"), A)))$,
);
#let r-proj = rule(
  name: "proj",
  $hasty(Γ, e, Π (fty(lb("f"), A)))$,
  $hasty(Γ, lb("f") med e, A)$,
);
#let r-tuple = rule(
  name: "tuple",
  $istup(Γ, E, lb("T"))$,
  $hasty(Γ, (E), Π lb("T"))$,
);
#let r-pi-nil = rule(
  name: "Π-nil",
  $istup(Γ, ·, ·)$,
);
#let r-pi-cons = rule(
  name: "Π-cons",
  $istup(Γ, E, lb("T"))$,
  $hasty(Γ, e, A)$,
  $istup(Γ, #$E, e$, #$lb("T"), fty(lb("f"), A)$)$,
);
#let r-let = rule(
  name: "let",
  $hasty(Γ, a, A)$,
  $hasty(#$Γ, x : A$, b, B)$,
  $hasty(Γ, elet(x, a, b), B)$,
);
#let r-cases = rule(
  name: "cases",
  $hasty(Γ, e, Σ lb("L"))$,
  $isebrs(Γ, lb("L"), M, A)$,
  $hasty(Γ, ecase(e, M), A)$,
);
#let r-sigma-nil = rule(
  name: "Σ-nil",
  $isebrs(Γ, ·, ·, A)$,
);
#let r-sigma-cons = rule(
  name: "Σ-cons",
  $isebrs(Γ, lb("L"), M, A)$,
  $hasty(#$Γ, x : B$, a, A)$,
  $isebrs(Γ, #$lb("L"), lty(lb("l"), B)$, #$M, ebr(lb("l"), x, a)$, A)$,
);
#let r-iter = rule(
  name: "iter",
  $hasty(Γ, a, A)$,
  $hasty(Γ, e, B + A)$,
  $hasty(Γ, eiter(a, x, e), B)$,
);

#let r-csigma-nil = rule(
  name: "Σ-nil",
  $kebrs(·, ·, A)$
)
#let r-csigma-cons = rule(
  name: "Σ-cons",
  $kebrs(cal(K), M, A)$,
  $hasty(#$Γ, x : B$, a, A)$,
  $kebrs(#$cal(K), clty(lb("l"), Γ, B)$, #$M, ebr(lb("l"), x, a)$, A)$
)