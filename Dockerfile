# SleepLoop Verification Container
#
# Reproduces the full build and verification from scratch.
# Every command below is auditable — nothing is hidden or pre-baked.
#
# What this does:
#   1. Installs Lean 4.28.0 (via elan, the official Lean version manager)
#   2. Copies the project source and fetches the Mathlib cache
#   3. Builds all ~2740 jobs from source
#   4. Installs verification tools (lean4checker, comparator, lean4export, landrun)
#   5. Runs ./scripts/validate.sh which checks everything
#
# Usage:
#   docker build -t sleeploop-verify .
#   docker run --rm sleeploop-verify              # run full validation
#   docker run --rm -it sleeploop-verify bash      # interactive shell
#
# Also works with Podman:
#   podman build -t sleeploop-verify .
#   podman run --rm sleeploop-verify
#
# comparator uses landrun (Linux landlock sandbox). On native Linux with
# kernel >= 5.13, all 8 checks pass. In Docker Desktop (Windows/macOS),
# landlock is unavailable so comparator shows SKIP — all other checks still run.

FROM ubuntu:24.04

ENV DEBIAN_FRONTEND=noninteractive

# ── System packages (all from Ubuntu's official repos) ───────────
RUN apt-get update && apt-get install -y --no-install-recommends \
      curl ca-certificates git golang-go build-essential && \
    rm -rf /var/lib/apt/lists/*

# ── Lean 4 via elan (official Lean version manager) ─────────────
#    https://github.com/leanprover/elan
RUN curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
      | sh -s -- -y --default-toolchain none
ENV PATH="/root/.elan/bin:${PATH}"

# ── Copy project source ─────────────────────────────────────────
WORKDIR /workspace
COPY lean-toolchain lakefile.toml lake-manifest.json SleepLoop.lean ./
COPY SleepLoop/ SleepLoop/

# Install the exact Lean version specified by the project
RUN elan install "$(cat lean-toolchain)"

# ── Fetch Mathlib cache (pre-built .olean files) ────────────────
#    This avoids rebuilding Mathlib's 1.5M lines from source.
#    The cache is fetched from leanprover-community's official CDN.
#    If unavailable, the build step below will compile Mathlib from source.
RUN lake exe cache get || true

# ── Build the project from source ───────────────────────────────
RUN lake build

# ── Verification tools ──────────────────────────────────────────
#
# All tools are cloned from their official repos and built from source.
# Version tags are pinned to match the project's Lean 4.28.0 toolchain.

# lean4checker: replays all declarations through a fresh Lean kernel
#   https://github.com/leanprover/lean4checker
RUN git clone --depth 1 --branch v4.28.0 \
      https://github.com/leanprover/lean4checker /tools/lean4checker && \
    cd /tools/lean4checker && lake build

# lean4export: exports Lean environment for external checking
#   https://github.com/leanprover/lean4export
RUN git clone --depth 1 --branch v4.28.0 \
      https://github.com/leanprover/lean4export /tools/lean4export && \
    cd /tools/lean4export && lake build

# landrun: Linux landlock sandbox (used by comparator)
#   https://github.com/Zouuup/landrun
RUN git clone --depth 1 --branch v0.1.15 \
      https://github.com/Zouuup/landrun /tools/landrun && \
    cd /tools/landrun && go build -o /root/go/bin/landrun ./cmd/landrun

# comparator: sandboxed proof verification (leanprover official)
#   https://github.com/leanprover/comparator
#   No version pin — comparator has its own lean-toolchain and handles
#   cross-version checking. Tested working against our v4.28.0 project.
RUN git clone --depth 1 \
      https://github.com/leanprover/comparator /tools/comparator && \
    cd /tools/comparator && lake build

# ── Add all tool binaries to PATH ───────────────────────────────
ENV PATH="/tools/lean4checker/.lake/build/bin:/tools/comparator/.lake/build/bin:/tools/lean4export/.lake/build/bin:/root/go/bin:${PATH}"

# ── Runtime files (after build so edits don't bust cache) ─────
COPY scripts/ scripts/
COPY comparator.json ./

# ── Default: run full validation ────────────────────────────────
CMD ["bash", "./scripts/validate.sh"]
