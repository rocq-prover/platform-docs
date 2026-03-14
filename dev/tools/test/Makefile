all: test-mkdoc

test-mkdoc:
	if [ -d mktoc/out ]; then rm -r mktoc/out; fi
	mkdir mktoc/out
	cp mktoc/example1.v mktoc/example2.v mktoc/out
	../mktoc mktoc/out/example1.v mktoc/out/example2.v
	@diff mktoc/out/example1.v mktoc/expected/example1.v || \
		printf "test-mkdoc example1.v FAILED\n" 1>&2 && \
		printf "test-mkdoc example1.v SUCCEEDED\n" 1>&2
	@diff mktoc/out/example2.v mktoc/expected/example2.v || \
		printf "test-mkdoc example2.v FAILED\n" 1>&2 && \
		printf "test-mkdoc example2.v SUCCEEDED\n" 1>&2
	rm -r mktoc/out
