.PHONY: check
check:
	nix fmt -- --ci
	python3 scripts/lint.py
	lake build
	lake test
	lake exe basis-report --check
	lake exe basis-report | diff -u docs/basis.md -

.PHONY: fmt
fmt:
	nix fmt

.PHONY: basis
basis:
	lake build basis-report
	lake exe basis-report > docs/basis.md

.PHONY: build
build:
	lake build ritsuryo
