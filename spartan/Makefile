TITLE=Base on TypeTopology
FILES := Group Semantic

default: $(FILES:%=html/%.html)

.SECONDEXPANSION:
html/%.md: src/$$(subst .,/,%).lagda.md
	agda --html --html-highlight=code $<

html/%.html: html/%.md
	echo '<!DOCTYPE HTML><html><head><meta charset="utf-8"><title>$(TITLE)</title><link rel="stylesheet" href="Agda.css"></head>' > $@
	pandoc -f markdown -t html $< >> $@
