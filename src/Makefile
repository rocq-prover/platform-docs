# Source: https://github.com/jscoq/coqdoc-template

.PHONY: all clean serve

COQDOC_AUTO=coqdoc.css

# Select all the .v files in the current directory, excluding node_modules/
FILES := $(shell find . -path './node_modules' -prune -o -name '*.v' -print)
FILES_HTML := $(FILES:.v=.html)

all: $(FILES_HTML)

%.html: %.v %.glob jscoqdoc
	./jscoqdoc $<
	mv $(<F:.v=.html) $@
	sed -i 's/\.\//\.\.\//' $@

%.glob: %.v
	coqc $<

clean:
	rm -f **/*.vo **/*.vok **/.*.aux **/*.glob **/*.vos $(FILES_HTML) $(COQDOC_AUTO)

node_modules: package.json package-lock.json
	npm i

serve: node_modules
	./node_modules/.bin/http-server .
