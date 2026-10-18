#!/usr/bin/env bash
# Single-command MVP verification for civ6-lean4.
#
# Runs, in order:
#   1. lake build                         (plain Lean/Std, no Mathlib)
#   2. lake build Civ6Verify.Bounds.MvpOptimality
#                                         (explicit, independent of root wiring)
#   3. search/synthetic.py --self-test    (Python synthetic model tests)
#   4. search/synthetic.py --check-fixture(fixture semantic self-check)
#   5. scripts/check-synthetic.py         (actual Lean output vs fixture)
#   6. search/mvp.py --self-test          (MVP Python executable tests)
#   7. search/mvp.py --check-fixture      (frozen MVP fixture replay)
#   8. scripts/check-mvp.py --self-test   (Lean vs Python/fixture cross-check,
#                                         incl. negative mismatch detection)
#   9. scripts/audit-axioms.py            (generated #print axioms probe)
#
# The MVP model and lower bound are conditional statements about
# `M_MVP(theta*, sigma)` in mvp/RULE-CONTRACT.md v2.1; none of this is a
# Civilization VI claim. See mvp/VALIDATION.md for the MVP validation scope.
#
# Toolchain: a working project-local scripts/lean-env (.tools/lean-4.25.0-linux)
# is preferred; otherwise lean/lake on PATH (e.g. elan) must report the version
# pinned in ./lean-toolchain.  This script never downloads a toolchain.
#
# Set VERIFY_TOOLCHAIN=project or VERIFY_TOOLCHAIN=path to force one source
# (mainly for testing the fallback); default is auto.
set -Eeuo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

usage() {
  cat <<'EOF'
usage: scripts/verify.sh [-h]

Environment:
  VERIFY_TOOLCHAIN=auto|project|path   toolchain source (default: auto)
EOF
}

case "${1:-}" in
  -h|--help) usage; exit 0 ;;
  "") ;;
  *) usage >&2; exit 2 ;;
esac

die() {
  printf 'verify: %s\n' "$*" >&2
  exit 1
}

FORCE="${VERIFY_TOOLCHAIN:-auto}"
case "$FORCE" in
  auto|project|path) ;;
  *) die "VERIFY_TOOLCHAIN must be auto, project, or path (got: $FORCE)" ;;
esac

# A stale ambient search path must not leak into the build or the probes.
unset LEAN_PATH LEAN_SRC_PATH

[[ -f lean-toolchain ]] || die "missing lean-toolchain"
PIN_RAW="$(tr -d '[:space:]' < lean-toolchain)"
PIN="${PIN_RAW##*:}"
PIN="${PIN#v}"
[[ -n "$PIN" ]] || die "cannot read a Lean version from lean-toolchain"

version_has_pin() {
  [[ "$1" == *"version $PIN"* ]]
}

MODE_KIND=""
MODE_LABEL=""
PROJECT_NOTE="project-local scripts/lean-env not usable"
PATH_NOTE="no lean/lake on PATH"

if [[ -x scripts/lean-env ]]; then
  if PROJECT_LEAN="$(scripts/lean-env lean --version 2>&1)" \
     && PROJECT_LAKE="$(scripts/lean-env lake --version 2>&1)" \
     && version_has_pin "$PROJECT_LEAN" \
     && version_has_pin "$PROJECT_LAKE"; then
    PROJECT_NOTE=""
  else
    PROJECT_NOTE="project-local scripts/lean-env does not provide Lean $PIN"
  fi
fi

if command -v lean >/dev/null 2>&1 && command -v lake >/dev/null 2>&1; then
  if PATH_LEAN="$(lean --version 2>&1)" \
     && PATH_LAKE="$(lake --version 2>&1)" \
     && version_has_pin "$PATH_LEAN" \
     && version_has_pin "$PATH_LAKE"; then
    PATH_NOTE=""
  else
    PATH_NOTE="lean/lake on PATH are not Lean $PIN"
  fi
fi

if [[ "$FORCE" != "path" && -z "$PROJECT_NOTE" ]]; then
  MODE_KIND="project"
  MODE_LABEL="project-local .tools (scripts/lean-env)"
  TOOLCHAIN_BIN="$(scripts/lean-env sh -c 'dirname "$(command -v lake)"')"
  [[ -n "$TOOLCHAIN_BIN" ]] || die "scripts/lean-env did not resolve a lake binary"
  export PATH="$TOOLCHAIN_BIN:$PATH"
elif [[ "$FORCE" != "project" && -z "$PATH_NOTE" ]]; then
  MODE_KIND="path"
  MODE_LABEL="PATH (elan/system lean + lake)"
  TOOLCHAIN_BIN="$(dirname "$(command -v lean)")"
  export PATH="$TOOLCHAIN_BIN:$PATH"
else
  {
    echo "verify: no usable Lean $PIN toolchain."
    if [[ -n "$PROJECT_NOTE" ]]; then echo "  $PROJECT_NOTE"; fi
    if [[ -n "$PATH_NOTE" ]]; then echo "  $PATH_NOTE"; fi
    echo "  Install elan (https://github.com/leanprover/elan) so lean/lake are on PATH,"
    echo "  or unpack Lean $PIN under .tools/lean-4.25.0-linux (research/TOOLCHAIN.md)."
    echo "  This script does not download toolchains."
  } >&2
  exit 1
fi

LEAN_VERSION_LINE="$(lean --version | head -n 1)"
LAKE_VERSION_LINE="$(lake --version | head -n 1)"
command -v python3 >/dev/null 2>&1 || die "python3 not found on PATH"

WORKDIR="$(mktemp -d "${TMPDIR:-/tmp}/civ6-verify.XXXXXX")"
cleanup() { rm -rf "$WORKDIR"; }
trap cleanup EXIT

step_fail() {
  printf 'verify: FAILED: %s (exit %s)\n' "$1" "$2" >&2
  exit "$2"
}

run_step() {
  local title="$1"
  shift
  printf '\n==> %s\n' "$title"
  local start=$SECONDS rc=0
  "$@" || rc=$?
  (( rc == 0 )) || step_fail "$title" "$rc"
  printf 'ok: %s (%ss)\n' "$title" "$((SECONDS - start))"
}

# check-synthetic.py hardcodes scripts/lean-env.  In PATH mode we must not edit
# that file, so generate a throwaway wrapper and inject its path into the
# module's LEAN_ENV global for this process only.
run_lean_fixture_check() {
  if [[ "$MODE_KIND" == "project" ]]; then
    python3 scripts/check-synthetic.py
    return
  fi

  local shim="$WORKDIR/lean-env"
  cat > "$shim" <<EOF
#!/usr/bin/env bash
set -euo pipefail
cd "$ROOT"
exec "\$@"
EOF
  chmod +x "$shim"
  echo "note: using a temporary lean-env shim for the rigid fixture checker"
  VERIFY_ROOT="$ROOT" VERIFY_LEAN_ENV="$shim" python3 - <<'PY'
import importlib.util
import os
import sys
from pathlib import Path

root = Path(os.environ["VERIFY_ROOT"])
path = root / "scripts" / "check-synthetic.py"
spec = importlib.util.spec_from_file_location("check_synthetic_verify", path)
module = importlib.util.module_from_spec(spec)
sys.modules[spec.name] = module
spec.loader.exec_module(module)
module.LEAN_ENV = Path(os.environ["VERIFY_LEAN_ENV"])
raise SystemExit(module.main([]))
PY
}

printf 'verify: toolchain %s\n' "$MODE_LABEL"
printf '  %s\n  %s\n  pin lean-toolchain: %s\n' "$LEAN_VERSION_LINE" "$LAKE_VERSION_LINE" "$PIN_RAW"

run_step "Lean build (plain Lean/Std, no Mathlib)" lake build
# Build the MVP lower bound explicitly: it is the module check-mvp.py's
# `#check` probe imports, and this keeps the step independent of whether the
# root module currently imports it (`Civ6Verify.lean` is owned elsewhere).
run_step "Lean build MvpOptimality (MVP lower bound)" lake build Civ6Verify.Bounds.MvpOptimality
run_step "Python synthetic model self-tests" python3 search/synthetic.py --self-test
run_step "Synthetic fixture semantic check" python3 search/synthetic.py --check-fixture
run_step "Lean-vs-fixture synthetic cross-check" run_lean_fixture_check
run_step "Python MVP executable self-tests" python3 search/mvp.py --self-test
run_step "MVP fixture replay" python3 search/mvp.py --check-fixture
run_step "MVP Lean-vs-Python/fixture cross-check" \
  python3 scripts/check-mvp.py --no-build --self-test
run_step "Policy variant self-tests" python3 search/policy.py --self-test
run_step "Policy fixture replay" python3 search/policy.py --check-fixture
run_step "Policy Lean probe" python3 search/policy.py --lean-probe
run_step "Cost-frontier self-tests" python3 search/cost_frontier.py --self-test
run_step "Cost-frontier fixture replay" python3 search/cost_frontier.py --check-fixture
run_step "Theorem axiom audit" python3 scripts/audit-axioms.py --no-build

printf '\nverify: PASS\n'
printf '  toolchain: %s\n' "$MODE_LABEL"
printf '  Lean: %s\n' "$LEAN_VERSION_LINE"
printf '  Note: validated artifacts are the synthetic benchmark and the conditional\n'
printf '        MVP model, not Civ6 rules.\n'
