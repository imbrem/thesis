#let ms(txt) = $sans(txt)$
#let mb(txt) = $bold(txt)$

#let ite(o, l, r) = $ms("if") #o thick { #l } ms("else") { #r }$
#let linl(v) = $ι_l med #v$
#let linr(v) = $ι_r med #v$
#let labort(v) = $ms("abort") #v$
#let seq = $; thick$
#let brb(ℓ, v) = $ms("br") #ℓ thick #v$
#let retb(v) = $ms("ret") #v$
#let caseexpr2(e, x, a, y, b) = $ms("case") #e thick {linl(#x) : #a seq linr(#y) : #b}$
#let casestmt2(e, x, s, y, t) = $ms("case") #e thick {linl(#x) : #s seq linr(#y) : #t}$
#let wbranch(ℓ, x, t) = $#ℓ (#x) : #t$
#let where(t, L) = $#t thick ms("where") {#L}$
#let letstmt(x, a, t) = $ms("let") #x = #a seq #t$
#let letexpr(x, a, e) = $ms("let") #x = #a seq #e$
#let bhyp(x, A, q: []) = $#x : #A^#q$
#let lhyp(ℓ, A) = $#ℓ (#A)$
#let hasty(Γ, ε, a, A) = $#Γ ⊢_#ε #a : #A$
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