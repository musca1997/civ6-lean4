#!/usr/bin/env python3
"""Rigorous axiom audit for the Civ6Verify Lean development.

Scope: every theorem constant under the `Civ6Verify` namespace that is visible
after importing the project modules.  Theorem names are discovered by Lean
itself (generated probe), not hardcoded, so new core/scenario declarations are
audited automatically.

Method
------
1. Static scan of `Civ6Verify.lean` and `Civ6Verify/**/*.lean` after removing
   comments and string literals.  `sorry`/`admit`, `axiom`/`constant`,
   `native_decide`/`Lean.ofReduceBool`, `implemented_by`/`extern`, and
   `debug.skipKernelTC` are rejected.
2. Generated Lean discovery probe: enumerate public and private theorem
   constants with `Lean.wasOriginallyTheorem`.  Public names are fed to a second
   generated probe containing one `#print axioms` command per theorem.
3. Private compiler-generated match-equation lemmas have mangled names that
   cannot be written in source syntax; their dependencies are collected with
   `Lean.collectAxioms` inside the discovery probe.
4. Only `propext` and `Quot.sound` are approved.  Any other axiom (including
   `sorryAx`, `Lean.ofReduceBool`, `Classical.choice`, or a project axiom) is a
   failure.

Exit codes: 0 pass, 1 audit failure, 2 setup/toolchain/Lean error.
"""

from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path
from typing import Any, Dict, List, Sequence, Set, Tuple

REPO_ROOT = Path(__file__).resolve().parents[1]
APPROVED_AXIOMS = frozenset({"propext", "Quot.sound"})

# token -> human-readable reason
FORBIDDEN = {
    "sorryAx": "proof contains sorryAx",
    "sorry": "proof contains sorry",
    "admit": "proof uses admit",
    "axiom": "custom axiom declaration",
    "constant": "custom constant/axiom declaration",
    "native_decide": "native_decide introduces native compiler trust",
    "Lean.ofReduceBool": "native/compiler reduction axiom",
    "implemented_by": "native implementation attribute",
    "extern": "extern/native declaration",
    "skipKernelTC": "kernel type checking disabled",
}
FORBIDDEN_RE = re.compile(
    r"\b(" + "|".join(re.escape(tok) for tok in sorted(FORBIDDEN, key=len, reverse=True)) + r")\b"
)


class AuditError(Exception):
    def __init__(self, message: str, code: int = 2) -> None:
        super().__init__(message)
        self.code = code


def project_sources() -> Tuple[List[Path], List[str]]:
    """Return Lean source files and their module names."""
    files: List[Path] = []
    root = REPO_ROOT / "Civ6Verify.lean"
    if root.is_file():
        files.append(root)
    subdir = REPO_ROOT / "Civ6Verify"
    if subdir.is_dir():
        files.extend(sorted(p for p in subdir.rglob("*.lean") if p.is_file()))
    modules: List[str] = []
    for path in files:
        module = ".".join(path.relative_to(REPO_ROOT).with_suffix("").parts)
        if module not in modules:
            modules.append(module)
    return files, modules


def strip_comments_and_strings(text: str) -> str:
    """Blank out comments/string literals while preserving line numbers."""
    out: List[str] = []
    i, n, depth = 0, len(text), 0
    in_string = False
    while i < n:
        c = text[i]
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_string:
            if c == "\\":
                out.append(" ")
                if i + 1 < n:
                    out.append("\n" if text[i + 1] == "\n" else " ")
                i += 2
            elif c == '"':
                in_string = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif text.startswith("--", i):
            j = text.find("\n", i)
            if j == -1:
                out.append(" " * (n - i))
                i = n
            else:
                out.append(" " * (j - i))
                out.append("\n")
                i = j + 1
        elif text.startswith("/-", i):
            depth = 1
            out.append("  ")
            i += 2
        elif c == '"':
            in_string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def static_scan(files: Sequence[Path]) -> List[str]:
    violations: List[str] = []
    for path in files:
        raw = path.read_text(encoding="utf-8")
        clean = strip_comments_and_strings(raw)
        for match in FORBIDDEN_RE.finditer(clean):
            token = match.group(1)
            line = clean.count("\n", 0, match.start()) + 1
            rel = path.relative_to(REPO_ROOT)
            violations.append(f"{rel}:{line}: {token} ({FORBIDDEN[token]})")
    return violations


def imports_block(modules: Sequence[str]) -> str:
    return "\n".join(f"import {m}" for m in modules)


def lean_string(value: str) -> str:
    escaped = value.replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n")
    return f'"{escaped}"'


def discovery_probe(modules: Sequence[str], public_path: Path, private_path: Path) -> str:
    return f"""import Lean
{imports_block(modules)}

open Lean

run_cmd do
  let env ← getEnv
  let mut publicNames : Array Name := #[]
  let mut privateNames : Array Name := #[]
  for (name, _) in env.constants.toList do
    if (`Civ6Verify).isPrefixOf name && wasOriginallyTheorem env name then
      publicNames := publicNames.push name
    else if (`_private.Civ6Verify).isPrefixOf name && wasOriginallyTheorem env name then
      privateNames := privateNames.push name
  let mut publicLines : Array String := #[]
  for name in publicNames.qsort (fun a b => a.toString < b.toString) do
    publicLines := publicLines.push name.toString
  let mut privateLines : Array String := #[]
  for name in privateNames.qsort (fun a b => a.toString < b.toString) do
    let axs ← collectAxioms name
    let rendered := String.intercalate "," (axs.toList.map toString)
    privateLines := privateLines.push s!"{{name}}|{{rendered}}"
  liftM (IO.FS.writeFile {lean_string(str(public_path))} (String.intercalate "\n" publicLines.toList ++ "\n"))
  liftM (IO.FS.writeFile {lean_string(str(private_path))} (String.intercalate "\n" privateLines.toList ++ "\n"))
"""


def print_probe(modules: Sequence[str], names: Sequence[str]) -> str:
    lines = [f"import Lean", imports_block(modules), ""]
    lines.extend(f"#print axioms {name}" for name in names)
    return "\n".join(lines) + "\n"


def resolve_lake(arg: str) -> List[str]:
    """Resolve a lake command, falling back to the project-local wrapper."""
    if arg != "lake":
        if shutil.which(arg) or Path(arg).is_file():
            return [arg]
        raise AuditError(f"lake executable not found: {arg}")
    found = shutil.which("lake")
    if found:
        return [found]
    wrapper = REPO_ROOT / "scripts" / "lean-env"
    if wrapper.is_file() and os.access(wrapper, os.X_OK):
        return [str(wrapper), "lake"]
    raise AuditError(
        "lake not found on PATH and project-local scripts/lean-env is unavailable; "
        "run scripts/verify.sh or install Lean 4.25.0"
    )


def run_command(cmd: Sequence[str], timeout: float, verbose: bool) -> subprocess.CompletedProcess:
    try:
        proc = subprocess.run(
            list(cmd),
            cwd=str(REPO_ROOT),
            capture_output=True,
            text=True,
            timeout=timeout,
        )
    except FileNotFoundError as exc:
        raise AuditError(f"command not found: {cmd[0]}") from exc
    except subprocess.TimeoutExpired as exc:
        raise AuditError(f"timed out after {exc.timeout}s: {' '.join(cmd)}") from exc
    if verbose:
        sys.stderr.write(proc.stdout)
        sys.stderr.write(proc.stderr)
    return proc


def tail(text: str, limit: int = 3000) -> str:
    text = text.strip()
    return text if len(text) <= limit else "…\n" + text[-limit:]


def join_wrapped_lines(output: str) -> List[str]:
    """Undo the message printer's indented line wrapping."""
    lines: List[str] = []
    for line in output.splitlines():
        if line[:1].isspace() and lines:
            lines[-1] = lines[-1] + " " + line.strip()
        elif line.strip():
            lines.append(line.strip())
    return lines


def read_public_names(path: Path) -> List[str]:
    if not path.is_file():
        return []
    return sorted({line.strip() for line in path.read_text(encoding="utf-8").splitlines() if line.strip()})


def read_private_axioms(path: Path) -> Dict[str, List[str]]:
    result: Dict[str, List[str]] = {}
    if not path.is_file():
        return result
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        name, _, rendered = line.strip().partition("|")
        result[name] = [a for a in rendered.split(",") if a]
    return result


def axioms_from_print(output: str, name: str) -> Tuple[bool, Set[str]]:
    """Return (found, axioms) for one theorem's #print axioms output."""
    none_marker = f"'{name}' does not depend on any axioms"
    dep_marker = f"'{name}' depends on axioms: ["
    for line in join_wrapped_lines(output):
        if none_marker in line:
            return True, set()
        idx = line.find(dep_marker)
        if idx != -1:
            rest = line[idx + len(dep_marker):]
            end = rest.find("]")
            if end == -1:
                return True, {rest.strip()}
            axes = [a.strip() for a in rest[:end].split(",") if a.strip()]
            return True, set(axes)
    return False, set()


def classify(axiom: str) -> str:
    if axiom == "sorryAx":
        return "forbidden: proof uses sorry"
    if axiom in ("Lean.ofReduceBool", "Lean.ofReduceNat"):
        return "forbidden: native_decide/compiler trust"
    if axiom == "Classical.choice":
        return "not approved: Classical.choice"
    return "not approved: custom axiom or unexpected core axiom"


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description="Audit Civ6Verify theorem axioms.")
    parser.add_argument("--no-build", action="store_true", help="use existing .olean files")
    parser.add_argument("--lake", default="lake", help="lake executable (default: lake)")
    parser.add_argument("--timeout", type=float, default=600.0, help="per-command timeout (s)")
    parser.add_argument("--json", action="store_true", help="machine-readable result")
    parser.add_argument("--verbose", action="store_true", help="echo Lean output and per-theorem results")
    parser.add_argument("--keep-probe", metavar="PATH", help="keep the generated #print axioms probe")
    args = parser.parse_args(list(argv) if argv is not None else None)

    files, modules = project_sources()
    result: Dict[str, Any] = {
        "ok": False,
        "publicTheorems": 0,
        "privateTheorems": 0,
        "approvedAxioms": sorted(APPROVED_AXIOMS),
        "axiomHistogram": {},
        "violations": [],
    }

    def finish(code: int) -> int:
        result["ok"] = code == 0
        if args.json:
            print(json.dumps(result, indent=2, ensure_ascii=False))
        return code

    try:
        if not files:
            raise AuditError("no Lean sources found under Civ6Verify")

        static_violations = static_scan(files)
        result["violations"].extend(static_violations)

        lake = resolve_lake(args.lake)

        if not args.no_build:
            proc = run_command([*lake, "build"], args.timeout, args.verbose)
            if proc.returncode != 0:
                raise AuditError(
                    f"lake build failed (exit {proc.returncode})\n{tail(proc.stderr or proc.stdout)}"
                )

        with tempfile.TemporaryDirectory(prefix="civ6-axiom-audit-") as tmp:
            tmp_path = Path(tmp)
            discover = tmp_path / "AxiomDiscover.lean"
            public_file = tmp_path / "public-theorems.txt"
            private_file = tmp_path / "private-theorems.txt"
            discover.write_text(
                discovery_probe(modules, public_file, private_file), encoding="utf-8"
            )
            proc = run_command([*lake, "env", "lean", str(discover)], args.timeout, args.verbose)
            if proc.returncode != 0:
                raise AuditError(
                    f"Lean discovery probe failed (exit {proc.returncode})\n"
                    f"{tail(proc.stderr or proc.stdout)}"
                )
            public = read_public_names(public_file)
            private = read_private_axioms(private_file)
            result["publicTheorems"] = len(public)
            result["privateTheorems"] = len(private)
            if not public:
                raise AuditError("Lean discovery probe found no public Civ6Verify theorems")

            for name, axioms in sorted(private.items()):
                bad = sorted(set(axioms) - APPROVED_AXIOMS)
                if bad:
                    detail = "; ".join(f"{a} ({classify(a)})" for a in bad)
                    result["violations"].append(f"private theorem {name}: {detail}")

            probe = tmp_path / "AxiomAudit.lean"
            probe.write_text(print_probe(modules, public), encoding="utf-8")
            if args.keep_probe:
                Path(args.keep_probe).write_text(probe.read_text(encoding="utf-8"), encoding="utf-8")
            proc = run_command([*lake, "env", "lean", str(probe)], args.timeout, args.verbose)
            if proc.returncode != 0:
                raise AuditError(
                    f"Lean #print axioms probe failed (exit {proc.returncode})\n"
                    f"{tail(proc.stderr or proc.stdout)}"
                )

        histogram: Dict[str, int] = {}
        for name in public:
            found, axioms = axioms_from_print(proc.stdout, name)
            if not found:
                result["violations"].append(f"{name}: no #print axioms line produced")
                continue
            bad = sorted(axioms - APPROVED_AXIOMS)
            key = "none" if not axioms else ", ".join(sorted(axioms))
            histogram[key] = histogram.get(key, 0) + 1
            if args.verbose:
                shown = "none" if not axioms else ", ".join(sorted(axioms))
                print(f"  {name}: {shown}", file=sys.stderr)
            if bad:
                detail = "; ".join(f"{a} ({classify(a)})" for a in bad)
                result["violations"].append(f"{name}: {detail}")
        result["axiomHistogram"] = dict(sorted(histogram.items()))

    except AuditError as exc:
        result["violations"].append(str(exc))
        if not args.json:
            print(f"AXIOM AUDIT ERROR: {exc}", file=sys.stderr)
        return finish(exc.code)
    except OSError as exc:
        result["violations"].append(str(exc))
        if not args.json:
            print(f"AXIOM AUDIT ERROR: {exc}", file=sys.stderr)
        return finish(2)

    if args.json:
        code = 0 if not result["violations"] else 1
        return finish(code)

    print(
        f"axiom audit: {result['publicTheorems']} public theorem constants "
        f"(#print axioms) + {result['privateTheorems']} private generated "
        f"theorem constants (collectAxioms)"
    )
    dist = ", ".join(f"{k}: {v}" for k, v in result["axiomHistogram"].items()) or "none"
    print(f"approved axioms {sorted(APPROVED_AXIOMS)}; dependency histogram: {dist}")
    if result["violations"]:
        for violation in result["violations"]:
            print(f"FAIL: {violation}", file=sys.stderr)
        return finish(1)
    print("PASS: no sorryAx, no custom axioms, no native compilation trust")
    return finish(0)


if __name__ == "__main__":
    sys.exit(main())
