.PHONY: all build b check c lint fmt fmt-check test tooling-test

all: build check

build:
	time lake build

b: build

lint:
	time lake lint

fmt:
	time python3 scripts/fmt.py

fmt-check:
	time python3 scripts/fmt.py --check

test:
	time lake exe kalman_regression

tooling-test:
	time python3 -m unittest discover -s scripts -p 'test_*.py'

check: lint
	time python3 -m unittest discover -s scripts -p 'test_*.py'
	time python3 scripts/fmt.py --check
	time lake exe kalman_regression

c: check
