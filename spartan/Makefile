TITLE=Base on TypeTopology
# Find all .lagda.md files in src/ and convert paths
LAGDA_FILES := $(shell find src -name "*.lagda.md" | sort)
FILES := $(LAGDA_FILES:src/%.lagda.md=%)
FILES := $(subst /,.,$(FILES))

default: $(FILES:%=html/%.html)

html/%.md: src/%.lagda.md
	agda --html --html-highlight=code $<

html/%.html: html/%.md
	echo '<!DOCTYPE HTML><html><head><meta charset="utf-8"><title>$(TITLE)</title><link rel="stylesheet" href="Agda.css"></head>' > $@
	pandoc -f markdown -t html $< >> $@
