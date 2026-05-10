# --- Typst thesis ---

LIB := $(shell find lib -name '*.typ' 2>/dev/null)
TYPST_SOURCES := $(shell find thesis -name '*.typ')
TYPST_PDFS := $(TYPST_SOURCES:.typ=.pdf)

# --- LaTeX papers ---

PAPER_DIR := papers/isotope
TEX_SOURCES := $(wildcard $(PAPER_DIR)/*.tex)
TEX_PDFS := $(TEX_SOURCES:.tex=.pdf)

# --- Targets ---

.PHONY: all thesis parts papers submodules clean todo help

thesis: thesis/main.pdf

parts: $(TYPST_PDFS)

all: parts papers

papers: $(TEX_PDFS)

submodules:
	git submodule update --init --recursive

# Each .typ depends on its own source, all .typ files in child directories, and lib.
.SECONDEXPANSION:
%.pdf: %.typ $$(shell find $$(dir $$*.typ) -name '*.typ') $(LIB)
	typst compile --root . $< $@

$(PAPER_DIR)/%.pdf: $(PAPER_DIR)/%.tex $(PAPER_DIR)/references.bib
	cd $(PAPER_DIR) && latexmk -pdf -interaction=nonstopmode $*.tex

todo:
	@python3 scripts/thesis.py todo

clean:
	find thesis -name '*.pdf' -delete
	cd $(PAPER_DIR) && latexmk -C

help:
	@echo "Usage: make [target]"
	@echo ""
	@echo "Build targets:"
	@echo "  thesis      Build thesis/main.pdf (default)"
	@echo "  parts       Build every .typ file under thesis/ as a standalone PDF"
	@echo "  papers      Build LaTeX papers"
	@echo "  all         Build parts + papers"
	@echo ""
	@echo "Single file:  make thesis/path/to/file.pdf"
	@echo ""
	@echo "Utilities:"
	@echo "  todo        List all #todo items in the thesis"
	@echo "  submodules  Clone/update git submodules"
	@echo "  clean       Remove generated PDFs and LaTeX aux files"
	@echo "  help        Show this help"
