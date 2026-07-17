.PHONY: all build test lint fixtures check shellcheck

all: check

build:
	lake build --wfail

test:
	lake test --wfail

lint:
	lake lint

fixtures:
	lake exe fmt-test --update-fixture --check Tests/Fixtures/*/*.leanfmt

shellcheck:
	shellcheck --severity=warning scripts/*.sh

check: build test lint fixtures
	lake exe fmt --check --check-exception --check-idempotent -r LeanFmt Tests/*.lean
	git diff --check

fmt:
	lake exe fmt -r LeanFmt Tests/*.lean
	make check
