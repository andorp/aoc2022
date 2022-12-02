idris2 = idris2

build: src aoc2022.ipkg FORCE
	$(idris2) --build aoc2022.ipkg

FORCE:

watch:
	while inotifywait -e close_write -r src; do $(idris2) --typecheck aoc2022.ipkg; done

clean:
	$(idris2) --clean aoc2022.ipkg
	rm -r build

typecheck:
	$(idris2) --typecheck aoc2022.ipkg

repl:
	rlwrap $(idris2) --repl aoc2022.ipkg

test: build FORCE
	./.build/exec/aoc2022
