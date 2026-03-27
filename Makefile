# --- Typst thesis ---

LIB := $(shell find lib -name '*.typ' 2>/dev/null)
TYPST_SOURCES := $(shell find thesis -name '*.typ')
TYPST_PDFS := $(TYPST_SOURCES:.typ=.pdf)

# --- LaTeX papers ---

PAPER_DIR := papers/isotope
TEX_SOURCES := $(wildcard $(PAPER_DIR)/*.tex)
TEX_PDFS := $(TEX_SOURCES:.tex=.pdf)

# --- Targets ---

.PHONY: all thesis parts papers submodules clean

thesis: thesis/main.pdf

parts: $(TYPST_PDFS)

all: parts papers

papers: $(TEX_PDFS)

submodules:
	git submodule update --init --recursive

%.pdf: %.typ $(LIB)
	typst compile --root . $< $@

$(PAPER_DIR)/%.pdf: $(PAPER_DIR)/%.tex $(PAPER_DIR)/references.bib
	cd $(PAPER_DIR) && latexmk -pdf -interaction=nonstopmode $*.tex

clean:
	find thesis -name '*.pdf' -delete
	cd $(PAPER_DIR) && latexmk -C
