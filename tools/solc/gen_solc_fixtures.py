#!/usr/bin/env python3
"""Generate (or check) the solc Yul-lowering fixtures used by `EvmYul/Solc/MatrixTests.lean`.

This implements Steps 1, 2 and 6 of `docs/SOLC_VYPER_PLAN.md` (Path A). The Lean build never runs
this script: it only reads the generated files, so `lake build` stays hermetic (TESTING.md 0.2).

What it does, for every compiler pinned in `tools/solc/solc-matrix.lock`:

1. downloads the static linux-amd64 binary into a cache directory outside the repository and
   **refuses it** unless its sha256 equals the pinned one (and checks `solc --version`);
2. compiles every program of `tools/solc/corpus/*.yul` with `--strict-assembly`, the lock file's
   EVM target, once without and once with `--optimize`; for the compilers whose extra column is
   `ssa`, also with the experimental `--experimental --via-ssa-cfg` code generator (unoptimized);
3. replays a fixed set of calldata points per cell on py-evm (pinned in `tools/vyper/oracle.lock`,
   verified and installed the same way, run through `tools/vyper/pyevm_oracle.py`) and records
   success, execution gas and storage slots 0 and 1: the independent-EVM oracle;
4. writes the cells into `EvmYul/Solc/Fixtures.lean`, and the corpus itself, as the *project's own
   Yul notation applied to the very same source text*, into `EvmYul/Solc/Corpus.lean`. The build
   therefore elaborates the compiled text with the project's Yul parser: the Yul model and the
   compiler read one source.

Corpus convention (checked here): a program is one Yul block `{ ... }`; every function definition
sits on its own line(s) starting with `function`, before any other statement; numbers are decimal.

Modes:
  (default)   regenerate both Lean files in place;
  --check     regenerate into memory, exit 1 if a checked-in file differs (drift) or if
              binaries.soliditylang.org lists a newer release than the pinned latest;
  --no-latest with --check: skip the newer-release query;
  --self-test offline checks of the helper functions.

Needs network access the first time (download) and for the latest-release query; never needed by
`lake build`. Exit status: 0 ok, 1 drift / newer release / hash mismatch / compile failure.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import subprocess
import sys
import urllib.request
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LOCK = REPO / "tools" / "solc" / "solc-matrix.lock"
CORPUS = REPO / "tools" / "solc" / "corpus"
OUT_FIX = REPO / "EvmYul" / "Solc" / "Fixtures.lean"
OUT_CORPUS = REPO / "EvmYul" / "Solc" / "Corpus.lean"
BASE_URL = "https://binaries.soliditylang.org/linux-amd64/"
SLOTS = [0, 1]
W = 2 ** 256

sys.path.insert(0, str(REPO / "tools" / "vyper"))
import gen_vyper_fixtures as vy  # noqa: E402  (shared: oracle install, lean_str, version order)


@dataclass(frozen=True)
class Pin:
    version: str
    binary: str
    sha256: str
    evm: str
    extra: str


def read_lock(path: Path = LOCK) -> list[Pin]:
    pins = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        version, binary, sha, evm, extra = line.split()
        pins.append(Pin(version, binary, sha, evm, extra))
    if not pins:
        sys.exit("lock file lists no compiler")
    return pins


def request(url: str) -> urllib.request.Request:
    """The download host rejects urllib's default user agent (HTTP 403)."""
    return urllib.request.Request(url.replace("+", "%2B"), headers={"User-Agent": "curl/8"})


def fetch_solc(pin: Pin, cache: Path) -> Path:
    """Download (once) and verify the pinned binary; a mismatching file is set aside and refused."""
    path = cache / pin.binary
    if not path.exists():
        print(f"downloading {BASE_URL + pin.binary}", file=sys.stderr)
        with urllib.request.urlopen(request(BASE_URL + pin.binary)) as r:
            path.write_bytes(r.read())
    got = vy.sha256_file(path)
    if got != pin.sha256:
        path.rename(path.with_name(path.name + ".rejected"))
        sys.exit(f"sha256 mismatch for {pin.binary}: pinned {pin.sha256}, got {got}; refused "
                 f"(file moved to {path.name}.rejected)")
    path.chmod(0o755)
    out = vy.run([str(path), "--version"])
    if f"Version: {pin.version}+commit." not in out:
        sys.exit(f"{path} reports {out!r}, expected {pin.version}")
    return path


def columns(pin: Pin) -> list[tuple[bool, str, list[str]]]:
    """(optimize, codegen, flags) per compiled column of this compiler."""
    cols = [(False, "legacy", []), (True, "legacy", ["--optimize"])]
    if pin.extra == "ssa":
        cols.append((False, "ssaCfg", ["--experimental", "--via-ssa-cfg"]))
    elif pin.extra != "-":
        sys.exit(f"unknown extra column {pin.extra!r} for solc {pin.version}")
    return cols


def compile_yul(exe: Path, src: Path, evm: str, flags: list[str]) -> str:
    out = vy.run([str(exe), "--strict-assembly", "--evm-version", evm, *flags, "--bin", str(src)])
    lines = out.splitlines()
    try:
        hexcode = lines[lines.index("Binary representation:") + 1].strip()
    except (ValueError, IndexError):
        sys.exit(f"no binary in solc output for {src}")
    if not re.fullmatch(r"(?:[0-9a-f]{2})+", hexcode):
        sys.exit(f"unexpected bytecode for {src}: {hexcode[:40]}")
    return hexcode


def split_program(text: str) -> tuple[list[tuple[str, str]], str]:
    """Split a corpus program into its function definitions (name, text) and the remaining block.

    Function definitions must come first, each starting on a line whose first token is
    `function`; a definition ends where the next line starting with `function` (or the first
    non-function statement line) begins, with braces balanced."""
    body = text.strip()
    if not (body.startswith("{") and body.endswith("}")):
        sys.exit("a corpus program must be a single Yul block")
    inner = body[1:-1].strip().splitlines()
    fns, rest, cur, depth = [], [], None, 0
    for line in inner:
        s = line.strip()
        if cur is None and s.startswith("function "):
            if rest:
                sys.exit("function definitions must precede every other statement")
            cur = s
        elif cur is not None:
            cur += " " + s
        else:
            rest.append(s)
            continue
        depth = cur.count("{") - cur.count("}")
        if depth == 0:
            m = re.match(r"function\s+([A-Za-z_$][A-Za-z0-9_$.]*)\s*\(", cur)
            if not m:
                sys.exit(f"cannot read the function name in {cur!r}")
            fns.append((m.group(1), cur))
            cur = None
    if cur is not None:
        sys.exit("unbalanced braces in a function definition")
    if re.search(r"0x", body):
        sys.exit("corpus numbers must be decimal (the Lean notation reads decimal literals)")
    return fns, "{ " + " ".join(rest) + " }"


def points(program: str) -> list[list[int]]:
    """Calldata points replayed on py-evm (word arguments). They mirror the sweeps of
    `MatrixTests.lean`; the loop/recursion counts stay small so every run halts quickly."""
    if program in ("if_store", "if_const"):
        return [[x] for x in (0, 1, 2, 255, 2 ** 128, 2 ** 255, W - 1)]
    if program == "for_sum":
        return [[n] for n in range(13)]
    if program == "call_inline":
        g = (0, 1, 2, 2 ** 128, W - 1)
        return [[a, b] for a in g for b in g]
    if program == "call_rec":
        return [[n] for n in range(13)]
    if program == "nested_call":
        return [[n] for n in range(9)]
    sys.exit(f"no oracle domain for corpus program {program}")


def run_oracle(py: Path, code_hex: str, pts: list[list[int]]) -> list:
    req = {"code": code_hex, "slot": 0, "slots": SLOTS,
           "points": [{"data": "".join(vy.word(a) for a in args), "x0": 0, "value": 0}
                      for args in pts]}
    p = subprocess.run([str(py), str(vy.ORACLE)], input=json.dumps(req), capture_output=True,
                       text=True)
    if p.returncode != 0:
        sys.exit(f"py-evm oracle failed:\n{p.stderr}")
    res = json.loads(p.stdout)
    return [(args, ok, gas, after) for args, (ok, gas, after, _out) in zip(pts, res, strict=True)]


def lean_ident(stem: str) -> str:
    return "prog_" + re.sub(r"[^A-Za-z0-9_]", "_", stem)


def generate_corpus(sources: list[Path]) -> str:
    lines = [
        "module",
        "",
        "public import EvmYul.Yul.YulNotation",
        "public import EvmYul.Solc.Fixture",
        "",
        "public section",
        "",
        "/-!",
        "# The solc corpus, read by the project's own Yul parser (generated; do not edit)",
        "",
        "Generated by `python3 tools/solc/gen_solc_fixtures.py` from `tools/solc/corpus/*.yul`. Each",
        "program below is the *same source text* that the pinned compilers compiled (see",
        "`EvmYul/Solc/Fixtures.lean`), elaborated with the project's Yul notation (`<s …>`, `<f …>`):",
        "function definitions go to the contract's function table, the remaining statements form the",
        "dispatcher block. `MatrixTests.lean` runs these on the Yul interpreter and the Yul gas meter",
        "and compares them with the compiled bytecode on the EVM.",
        "-/",
        "",
        "namespace EvmYul.Solc",
        "",
        "open EvmYul.Yul Ast Notation",
        "",
    ]
    names = []
    for src in sources:
        fns, main = split_program(src.read_text())
        ident = lean_ident(src.stem)
        names.append((src.stem, ident))
        fn_terms = ", ".join(f"⟨{vy.lean_str(n)}, <f {t} >⟩" for n, t in fns)
        lines += [
            f"/-- `tools/solc/corpus/{src.name}`. -/",
            f"def {ident} : YulContract :=",
            f"  ⟨<s {main} >,",
            f"   List.toFinmap ([{fn_terms}] : List (Σ _ : YulFunctionName, FunctionDefinition))⟩",
            "",
        ]
    lines += [
        "/-- Corpus program by name (file stem). -/",
        "def corpusContract : String → Option YulContract",
    ]
    lines += [f"  | {vy.lean_str(stem)} => some {ident}" for stem, ident in names]
    lines += ["  | _ => none", "", "/-- The corpus program names, in file order. -/",
              "def corpusNames : List String := [" + ", ".join(vy.lean_str(s) for s, _ in names)
              + "]", "", "end EvmYul.Solc", ""]
    return "\n".join(lines)


def generate(cache: Path) -> tuple[str, str]:
    pins = read_lock()
    oracle_pin = vy.read_lock(vy.ORACLE_LOCK)[-1]
    py = vy.install_oracle(oracle_pin, cache)
    sources = sorted(CORPUS.glob("*.yul"))
    if not sources:
        sys.exit("empty corpus")
    cells = []
    for pin in pins:
        exe = fetch_solc(pin, cache)
        commit = vy.run([str(exe), "--version"]).split("+commit.")[1].split(".")[0]
        for src in sources:
            split_program(src.read_text())  # enforce the corpus convention
            for optimize, codegen, flags in columns(pin):
                code = compile_yul(exe, src, pin.evm, flags)
                oracle = run_oracle(py, code, points(src.stem))
                cells.append((pin, commit, src.stem, vy.sha256_file(src), optimize, codegen, code,
                              oracle))
    lines = [
        "module",
        "",
        "public import EvmYul.Solc.Fixture",
        "",
        "public section",
        "",
        "/-!",
        "# solc Yul-lowering fixtures (generated; do not edit)",
        "",
        "Generated by `python3 tools/solc/gen_solc_fixtures.py` from `tools/solc/corpus/*.yul` and the",
        "compilers pinned in `tools/solc/solc-matrix.lock` (binary sha256 verified), with",
        "`--strict-assembly` and the lock file's EVM target. Each cell's `oracle` points were executed",
        "on py-evm (Cancun, `tools/vyper/oracle.lock`), an EVM implementation independent of this",
        "project. `lake run checkSolcFixtures` regenerates and diffs this file.",
        "The compiler output is an untrusted test input (`TCB.md`): it can make a test fail, never a",
        "theorem true.",
        "-/",
        "",
        "namespace EvmYul.Solc",
        "",
        "/-- Every compiled cell: pinned compiler × corpus program × column. -/",
        "@[expose] def fixtures : List Cell := [",
    ]
    body = []
    for pin, commit, name, src_sha, optimize, codegen, code, oracle in cells:
        body.append("\n".join([
            "  { solc := " + vy.lean_str(pin.version) + ", commit := " + vy.lean_str(commit) + ",",
            "    binarySha256 := " + vy.lean_str(pin.sha256) + ",",
            f"    evmVersion := {vy.lean_str(pin.evm)}, optimize := {str(optimize).lower()}, "
            f"codegen := .{codegen},",
            f"    program := {vy.lean_str(name)}, sourceSha256 := {vy.lean_str(src_sha)},",
            "    runtimeHex := " + vy.lean_str(code) + ",",
            "    oracle := [" + ",\n      ".join(
                f"⟨{args}, {str(ok).lower()}, {gas}, {after}⟩" for args, ok, gas, after in oracle)
            + "] }",
        ]))
    lines.append(",\n".join(body) + " ]")
    lines += ["", "/-- The pinned latest compiler (last line of the lock file). -/",
              f"def pinnedLatest : String := {vy.lean_str(pins[-1].version)}", "",
              "/-- The pinned compiler versions, in lock-file order. -/",
              "def pinnedVersions : List String := ["
              + ", ".join(vy.lean_str(p.version) for p in pins) + "]", "",
              "/-- sha256 of every corpus source, by program name (checked against the cells). -/",
              "def corpusSha256 : List (String × String) := ["
              + ", ".join(f"({vy.lean_str(s.stem)}, {vy.lean_str(vy.sha256_file(s))})"
                          for s in sources) + "]", "",
              "/-- The storage slots recorded by the oracle, in order. -/",
              f"def oracleSlots : List Nat := {SLOTS}", "",
              "end EvmYul.Solc", ""]
    return "\n".join(lines), generate_corpus(sources)


def latest_release() -> str:
    with urllib.request.urlopen(request(BASE_URL + "list.json")) as r:
        return json.load(r)["latestRelease"]


def self_test() -> int:
    """Offline checks of the pure helpers (run by `lake run checkSolcFixtures` first)."""
    fns, main = split_program("{\n  function g(a) -> r { r := a }\n  sstore(0, g(1))\n}\n")
    fns2, _ = split_program("{\n function f(a) -> r {\n  r := a\n }\n f(2)\n}")
    cases = [
        (fns, [("g", "function g(a) -> r { r := a }")]),
        (main, "{ sstore(0, g(1)) }"),
        (fns2, [("f", "function f(a) -> r { r := a }")]),
        (lean_ident("call-rec"), "prog_call_rec"),
        (columns(Pin("0.8.37", "b", "h", "cancun", "ssa"))[-1][1], "ssaCfg"),
        (len(columns(Pin("0.8.13", "b", "h", "london", "-"))), 2),
        (vy.newer_release("0.8.37", "0.8.38"), True),
        (vy.newer_release("0.8.37", "0.8.37"), False),
    ]
    bad = [i for i, (got, want) in enumerate(cases) if got != want]
    for txt in ("{ sstore(0, 1)\n function g() { } }", "{ sstore(0, 0x10) }"):
        try:
            split_program(txt)
            bad.append(txt)
        except SystemExit:
            pass
    if bad:
        print(f"self-test failed on cases {bad}", file=sys.stderr)
        return 1
    print(f"self-test: {len(cases) + 2} helper cases pass")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--no-latest", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--cache", type=Path,
                    default=Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
                    / "evmyul-solc")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    args.cache.mkdir(parents=True, exist_ok=True)
    fixtures, corpus = generate(args.cache)
    if not args.check:
        OUT_FIX.parent.mkdir(parents=True, exist_ok=True)
        OUT_FIX.write_text(fixtures)
        OUT_CORPUS.write_text(corpus)
        print(f"wrote {OUT_FIX.relative_to(REPO)} and {OUT_CORPUS.relative_to(REPO)}")
        return 0
    status = 0
    for path, text in ((OUT_FIX, fixtures), (OUT_CORPUS, corpus)):
        if not path.exists() or path.read_text() != text:
            print(f"DRIFT: {path.relative_to(REPO)} differs from a fresh generation; rerun the "
                  "generator and review the diff", file=sys.stderr)
            status = 1
        else:
            print(f"{path.relative_to(REPO)} is up to date")
    if not args.no_latest:
        pinned, latest = read_lock()[-1].version, latest_release()
        if vy.newer_release(pinned, latest):
            print(f"NEWER RELEASE: solc {latest} on binaries.soliditylang.org, pinned latest is "
                  f"{pinned}; add it to the lock file and regenerate", file=sys.stderr)
            status = 1
        else:
            print(f"pinned latest {pinned} is the newest release ({latest})")
    return status


if __name__ == "__main__":
    sys.exit(main())
