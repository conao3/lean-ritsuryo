.PHONY: check
check:
	nix fmt -- --ci
	python3 scripts/lint.py
	python3 scripts/gen_holidays.py --check
	lake build
	lake test
	python3 scripts/test_cli.py .lake/build/bin/ritsuryo
	lake exe basis-report --check
	lake exe basis-report | diff -u docs/basis.md -

.PHONY: fmt
fmt:
	nix fmt

.PHONY: basis
basis:
	lake build basis-report
	lake exe basis-report > docs/basis.md

.PHONY: holidays
holidays:
	python3 scripts/gen_holidays.py

.PHONY: fetch-holidays
fetch-holidays:
	python3 scripts/gen_holidays.py --fetch

.PHONY: build
build:
	lake build ritsuryo
