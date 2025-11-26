TITLE=Base on TypeTopology
FILES := sp-0000 sp-0001 sp-0002

default: $(FILES:%=html/%.html)

.SECONDEXPANSION:
html/%.md: src/$$(subst .,/,%).lagda.md
	agda --html --html-highlight=code $<

html/%.html: html/%.md
	echo '<!DOCTYPE HTML><html><head><meta charset="utf-8"><title>$(TITLE)</title><link rel="stylesheet" href="Agda.css"></head>' > $@
	pandoc -f markdown -t html $< >> $@
