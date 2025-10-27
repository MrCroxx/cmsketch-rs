SHELL := /bin/bash
.PHONY: deps check test test-ignored test-all all fast monitor clear madsim

all: check test

deps:
	./scripts/install-deps.sh

check:
	typos
	shellcheck ./scripts/*
	cargo sort -w
	cargo fmt --all
	cargo clippy --all-targets

udeps:
	cargo udeps --workspace

test:
	RUST_BACKTRACE=1 cargo nextest run --all
	RUST_BACKTRACE=1 cargo test --doc

taplo:
	taplo fmt

ffmt:
	cargo +nightly fmt --all -- --config-path rustfmt.nightly.toml
