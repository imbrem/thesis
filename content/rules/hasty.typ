#import "../../syntax.typ": *

// Rules for Γ ⊢ a : A

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

// Congruence rules for Γ ⊢_Eq a ≈ b : A

#let req = ms("Eq")

#let r-e-var = rule(
  name: "var",
  $Γ med x = A$,
  $tyeq(Γ, req, x, x, A)$,
)
#let r-e-coe = rule(
  name: "coe",
  $tyeq(Γ, req, a, a', A)$,
  $tywk(A, A')$,
  $tyeq(Γ, req, a, a', A')$,
)
#let r-e-app = rule(
  name: "app",
  $isfn(Γ, f, A, B)$,
  $tyeq(Γ, req, a, a', A)$,
  $tyeq(Γ, req, f med a, f med a', B)$,
)
#let r-e-inj = rule(
  name: "inj",
  $tyeq(Γ, req, a, a', A)$,
  $tyeq(Γ, req, lb("l") med a, lb("l") med a', Σ (lty(lb("l"), A)))$,
)
#let r-e-proj = rule(
  name: "proj",
  $tyeq(Γ, req, e, e', Π (fty(lb("f"), A)))$,
  $tyeq(Γ, req, lb("f") med e, lb("f") med e', A)$,
)
#let r-e-tuple = rule(
  name: "tuple",
  $tupref(Γ, req, E, E', lb("T"))$,
  $tyeq(Γ, req, (E), (E'), Π lb("T"))$,
)
#let r-e-pi-nil = rule(
  name: "Π-nil",
  $tupref(Γ, req, ·, ·, ·)$,
)
#let r-e-pi-cons = rule(
  name: "Π-cons",
  $tupref(Γ, req, E, E', lb("T"))$,
  $tyeq(Γ, req, e, e', A)$,
  $tupref(Γ, req, #$E, e$, #$E', e'$, #$lb("T"), fty(lb("f"), A)$)$,
)
#let r-e-let = rule(
  name: "let",
  $tyeq(Γ, req, a, a', A)$,
  $tyeq(#$Γ, x : A$, req, b, b', B)$,
  $tyeq(Γ, req, elet(x, a, b), elet(x, a', b'), B)$,
)
#let r-e-cases = rule(
  name: "cases",
  $tyeq(Γ, req, e, e', Σ lb("L"))$,
  $ebrseq(Γ, lb("L"), req, M, M', A)$,
  $tyeq(Γ, req, ecase(e, M), ecase(e', M'), A)$,
)
#let r-e-sigma-nil = rule(
  name: "Σ-nil",
  $ebrseq(Γ, ·, req, ·, ·, ·)$,
)
#let r-e-sigma-cons = rule(
  name: "Σ-cons",
  $ebrseq(Γ, lb("L"), req, M, M', A)$,
  $tyeq(#$Γ, x : A$, req, a, a', A)$,
  $ebrseq(
    Γ, #$lb("L"), lty(lb("l"), A)$, req,
    (#$M, ebr(lb("l"), x, a)$), (#$M', ebr(lb("l"), x, a')$),
    A
  )$,
)
#let r-e-iter = rule(
  name: "iter",
  $tyeq(Γ, req, a, a', A)$,
  $tyeq(Γ, req, e, e', B + A)$,
  $tyeq(Γ, req, eiter(a, x, e), eiter(e', x, a'), B)$,
)

// Congruence rules for Γ ⊢_R a ->> b : A

#let rref = ms("R")