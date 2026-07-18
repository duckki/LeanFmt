.PHONY: all build test lint fixtures check shellcheck

all: check

build:
	time lake build --wfail

test:
	time lake test --wfail

lint:
	time lake lint

fixtures:
	time lake exe fmt-test --update-fixture --check Tests/Fixtures/*/*.leanfmt

shellcheck:
	shellcheck --severity=warning scripts/*.sh

check: build test lint fixtures
	time lake exe fmt --check --check-exception --check-idempotent -r LeanFmt
	git diff --check

fmt:
	time lake exe fmt -r LeanFmt
	make check
