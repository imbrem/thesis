// == Fonts ==

#let ms(txt) = $sans(txt)$
#let mb(txt) = $bold(txt)$
#let lb(txt, annot : none) = $mono(txt)_annot$

// == Branding ==

// Flat
#let while-flat(..xs) = if xs.pos().at(0, default: none) == none { 
    $ms("IMP")$ 
  } else { 
    $ms("IMP")[#xs.pos().at(0)]$ 
  }
#let rtl-flat(..xs) = if xs.pos().at(0, default: none) == none { 
    $ms("RTL")$ 
  } else { 
    $ms("RTL")[#xs.pos().at(0)]$ 
  }
#let ssa-a-flat(..xs) = if xs.pos().at(0, default: none) == none { 
    $ms("SSA")$ 
  } else { 
    $ms("SSA")[#xs.pos().at(0)]$ 
  }
#let rtl-a-flat(..xs) = if xs.pos().at(0, default: none) == none { 
    $ms("RTL")_ms("A")$ 
  } else { 
    $ms("RTL")_ms("A")[#xs.pos().at(0)]$ 
  }

// λ
#let rtl-calc(..xs) = if xs.pos().at(0, default: none) == none { 
    $λ_ms("rtl")$ 
  } else { 
    $λ_ms("rtl")[#xs.pos().at(0)]$ 
  }

#let grtl-calc(..xs) = if xs.pos().at(0, default: none) == none { 
    $λ_ms("rtl")^*$ 
  } else { 
    $λ_ms("rtl")^*[#xs.pos().at(0)]$ 
  }

#let ssa-calc(..xs) = if xs.pos().at(0, default: none) == none { 
    $λ_ms("ssa")$ 
  } else { 
    $λ_ms("ssa")[#xs.pos().at(0)]$ 
  }

#let gssa-calc(..xs) = if xs.pos().at(0, default: none) == none { 
    $λ_ms("ssa")^*$ 
  } else { 
    $λ_ms("ssa")^*[#xs.pos().at(0)]$ 
  }

#let iter-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("iter")$
} else {
  $λ_ms("iter")[#xs.pos().at(0)]$
}

#let case-calc(..xs) = if xs.pos().at(0, default: none) == none {
  $λ_ms("case")$
} else {
  $λ_ms("case")[#xs.pos().at(0)]$
}

// == Tokens ==

// Keywords

// Basic
#let klet = $ms("let")$
#let kbr = $ms("br")$
#let kcase = $ms("case")$
#let kiter = $ms("iter")$

// Sugar
#let kif = $ms("if")$
#let kelse = $ms("else")$
#let kwhile = $ms("while")$
#let kmut = $ms("mut")$
#let kabort = $ms("abort")$
#let kret = $ms("ret")$
#let kswitch = $ms("switch")$

// Standard names
#let ninl = $lb("i")_lb("l")$
#let ninr = $lb("i")_lb("r")$
#let nbr = $lb("b")$
#let ncn = $lb("c")$

// Types
#let tzero = $mb("0")$
#let tunit = $mb("1")$
#let tbool = $mb("2")$
#let tlist(A) = $mb("List") med #A$

// Injections and projections
#let linj = $ι_lb("l")$
#let rinj = $ι_lb("r")$

#let lpi = $π_lb("l")$
#let rpi = $π_lb("r")$

// Orders
#let sle(X) = $scripts(≤)_#X$

// Finite sets
#let kfin = $ms("Fin")$
#let fin(n) = $kfin #n$
#let kfcanon = $α_ms("Fin")^+$
#let fcanon(n, m) = $kfcanon(n, m)$

// Collections
#let cix(a) = $ms("ix")(#a)$
#let sdiff = $backslash$
#let csel(a, i) = $#a [#i]$
#let crem(a, i) = $#a sdiff #i$
#let cmap = $op("⟨$⟩")$
#let capp = $op("⟨⋆⟩")$
#let czip = $op("⟨,⟩")$
#let crix = $op("⟨#⟩")$
#let cfam = $ms("Fam")$
#let cthin = $ms("Thin")$
#let cperm = $ms("Perm")$
#let hfam(A, B) = $cfam(#A, #B)$
#let hthin(A, B) = $cthin(#A, #B)$
#let hperm(A, B) = $cperm(#A, #B)$

#let lthin(a, b) = $lpi (#a, #b)$
#let rthin(a, b) = $rpi (#a, #b)$

#let fnum(n) = $lb("p")_#n$
#let inum(n) = $lb("i")_#n$
#let fexpr(f, e) = $#f : #e$

// Lists
#let lnil = $[ med ]$
#let llen(A) = $|#A|$
// A single math "+" glyph as content
#let mplus = $+$

// Compact “++” built by overlaying two pluses
#let lcat = math.op(
  box(width: 1.0em, height: 0.7em)[
    #place(center,  dx: -0.15em, mplus)
    #place(center,  dx: 0.15em, mplus)
  ]
)

#let lsnoc = $op(":+")$

#let compat(C) = $;_#C$
#let famcomp = compat(ms("Fam"))

// Sets
#let site(c, t, f) = $ms("if") #c ms("then") #t ms("else") #f$
#let icol(a) = $bold(upright(#a))$
#let sfam(A) = $bold(upright(#A))$
#let pset(X) = $cal(P)(X)$

// Categories
#let cset = $ms("Set")$
#let cposet = $ms("Poset")$

#let piinj(A, B, i) = $ms("inj")(#A, #B, #i)$
#let ahm(C) = $scripts(->)_#C$
#let opc(C) = $#C^ms("op")$
#let opm(f) = $#f^ms("op")$
#let scat(C) = $sfam(cal(#C))$
#let munit = $upright(I)$

#let ntag(n, A) = $n · A$

// Punctuation
#let seq = $; thick$
#let ovrd = $triangle.stroked.small.l$

// == Syntax ==

// Syntax for expressions
  
/// A branch in a case expression
#let ebr(ℓ, x, b) = $#ℓ (#x) : #b$

/// A let expression
#let elet(x, a, e) = $klet #x = #a seq #e$

/// A case expression
#let ecase(e, B) = $kcase #e thick { #B }$

/// An iteration expression
#let eiter(e, x, b) = $kiter #e thick { #ebr(ncn, x, b) }$

// Statements

/// An unconditional branch
#let brb(ℓ, ..vs) = if vs.pos().len() == 0 {
  $kbr #ℓ$
} else {
  $kbr #ℓ thick #vs.pos().at(0)$
}

/// A let statement
#let slet(x, a, t) = $klet #x = #a seq #t$

/// A case statement
#let scase(e, B) = $kcase #e thick { #B }$

/// A branch in a case statement
#let sbr(ℓ, x, b) = $#ℓ (#x) : #b$

#let gbr(ℓ, x, b) = $#ℓ (#x) : #b$

/// A labelled basic block
#let lbb(ℓ, x, t) = $#ℓ (#x) : #t$

// Syntax sugar

/// A return statement
#let retb(v) = $kret #v$

/// An if-then-else
#let ite(o, l, r) = $kif #o thick { #l } kelse { #r }$

/// A switch statement
#let sswitch(e, B) = $kswitch #e thick { #B }$

/// A branch in a switch statement
#let ssbr(ℓ, b) = $#ℓ : #b$

/// A binary case expression
#let ecase2(e, x, a, y, b) = ecase(e, $ebr(ninl, #x, #a) seq ebr(ninr, #y, #b)$)

/// A binary case statement
#let scase2(e, x, s, y, t) = scase(e, $sbr(ninl, #x, #s) seq  sbr(ninr, #y, #t)$)

/// A φ-expression
#let eϕ(branches) = $ϕ thick { #branches }$

// Judgements

#let bhyp(x, A, ..vs) = $#x : #A^(#vs.pos().at(0, default: none))$
#let lhyp(ℓ, A) = $#ℓ (#A)$
#let hasty(Γ, a, A) = $#Γ ⊢ #a : #A$
#let haslb(Γ, r, L) = $#Γ ⊢ #r triangle.stroked.small.r #L$
#let issubst(γ, Γ, Δ) = $#γ : #Γ => #Δ$
#let lbsubst(Γ, σ, L, K) = $#Γ ⊢ #σ : #L arrow.r.long.squiggly #K$
#let isop(f, A, B, ε) = $#f : #A ->^#ε #B$
#let tmeq(Γ, ε, a, b, A) = $#Γ ⊢_#ε #a equiv #b : #A$
#let lbeq(Γ, r, s, L) = $#Γ ⊢ #r equiv #s triangle.stroked.small.r #L$
#let tmseq(γ, γp, Γ, Δ) = $#γ equiv #γp : #Γ => #Δ$
#let lbseq(σ, σp, Γ, L, K) = $#Γ ⊢ #σ equiv #σp : #L arrow.r.long.squiggly #K$
#let cfgsubst(branches) = $⟨#branches⟩$
#let lupg(γ) = $upright(↑)#γ$
#let rupg(γ) = $#γ upright(↑)$