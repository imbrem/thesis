// == Fonts ==

#let ms(txt) = $sans(txt)$
#let mb(txt) = $bold(txt)$
#let lb(txt, annot : none) = $mono(txt)_annot$

// == Branding ==

// Flat
#let while-flat = $ms("IMP")$
#let rtl-flat = $ms("RTL")$
#let ssa-flat = $ms("SSA")$
#let ssa-a-flat = $ms("SSA")_ms("A")$
#let rtl-a-flat = $ms("RTL")_ms("A")$

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

// Categories
#let opc(C) = $#C^ms("op")$
#let opm(f) = $#f^ms("op")$

// Punctuation
#let seq = $; thick$

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