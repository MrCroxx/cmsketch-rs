SHELL := /bin/bash
.PHONY: deps check test test-ignored test-all all fast monitor clear madsim

deps:
	./scripts/install-deps.sh

check:
	typos
	shellcheck ./scripts/*
	./.github/template/generate.sh
	cargo sort -w
	cargo fmt --all
	cargo clippy --all-targets

udeps:
	cargo udeps --workspace

test:
	RUST_BACKTRACE=1 cargo nextest run --all
	RUST_BACKTRACE=1 cargo test --doc

ffmt:
	cargo +nightly fmt --all -- --config-path rustfmt.nightly.toml

all: check test

