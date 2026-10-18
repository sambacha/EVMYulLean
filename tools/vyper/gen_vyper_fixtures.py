#!/usr/bin/env python3
"""Generate (or check) the Vyper bytecode fixtures used by `EvmYul/Vyper/FixtureTests.lean`.

This is option V1 of `docs/SOLC_VYPER_PLAN.md` (bytecode level); the execution plan is
`docs/VYPER_V1_PLAN.md`. The Lean build never runs this script: it only reads the generated file
`EvmYul/Vyper/Fixtures.lean`, so `lake build` stays hermetic (TESTING.md rule 0.2).

What it does, for every compiler pinned in `tools/vyper/vyper-matrix.lock`:

1. downloads the compiler wheel into a cache directory outside the repository and **refuses it**
   unless its sha256 equals the pinned one;
2. installs it into a private virtual environment (one per version) in the same cache;
3. compiles every contract in `tools/vyper/corpus/` with `--evm-version cancun` (the fork this
   project's executable EVM runs), once with the default (legacy) code generator and once with
   Venom (`--experimental-codegen`);
4. records the runtime bytecode, the method identifiers, Vyper's own per-function gas estimate
   (`--show-gas-estimates`), the storage layout and the source loop bound (`bound=N`);
5. replays a fixed set of calls per cell on py-evm (pinned in `tools/vyper/oracle.lock`, verified
   and installed the same way, run through `tools/vyper/pyevm_oracle.py`) and records success,
   execution gas, storage and return data: the independent-EVM oracle of the tests' section 7;
6. writes all cells, in a fixed order, into `EvmYul/Vyper/Fixtures.lean`.

Modes:
  (default)   regenerate `EvmYul/Vyper/Fixtures.lean` in place;
  --check     regenerate into memory and exit 1 if the checked-in file differs (drift), or if PyPI
              has a newer stable Vyper than the last (latest) entry of the lock file;
  --no-latest with --check: skip the PyPI "newer release" query (drift check only);
  --self-test offline checks of the helper functions (version order, bound parsing, escaping).

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
import venv
from dataclasses import dataclass
from pathlib import Path

REPO = Path(__file__).resolve().parents[2]
LOCK = REPO / "tools" / "vyper" / "vyper-matrix.lock"
ORACLE_LOCK = REPO / "tools" / "vyper" / "oracle.lock"
ORACLE = REPO / "tools" / "vyper" / "pyevm_oracle.py"
CORPUS = REPO / "tools" / "vyper" / "corpus"
OUT = REPO / "EvmYul" / "Vyper" / "Fixtures.lean"
EVM_VERSION = "cancun"
CODEGENS = (("legacy", []), ("venom", ["--experimental-codegen"]))


@dataclass(frozen=True)
class Pin:
    version: str
    wheel: str
    sha256: str
    url: str


def read_lock(path: Path = LOCK) -> list[Pin]:
    pins = []
    for line in path.read_text().splitlines():
        line = line.strip()
        if not line or line.startswith("#"):
            continue
        version, wheel, sha, url = line.split()
        pins.append(Pin(version, wheel, sha, url))
    if not pins:
        sys.exit("lock file lists no compiler")
    return pins


def sha256_file(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def fetch_wheel(pin: Pin, cache: Path) -> Path:
    """Download (once) and verify the pinned wheel; a mismatching file is set aside and refused."""
    path = cache / pin.wheel
    if not path.exists():
        print(f"downloading {pin.url}", file=sys.stderr)
        with urllib.request.urlopen(pin.url) as r:
            path.write_bytes(r.read())
    got = sha256_file(path)
    if got != pin.sha256:
        path.rename(path.with_name(path.name + ".rejected"))
        sys.exit(f"sha256 mismatch for {pin.wheel}: pinned {pin.sha256}, got {got}; refused "
                 f"(file moved to {path.name}.rejected)")
    return path


def make_env(pin: Pin, cache: Path, name: str) -> Path:
    """A private virtual environment with the verified wheel installed; returns its `bin`."""
    env = cache / name
    marker = env / ".installed"
    if not marker.exists():
        wheel = fetch_wheel(pin, cache)
        venv.create(env, with_pip=True, clear=True)
        subprocess.run([str(env / "bin" / "pip"), "install", "-q", str(wheel)], check=True)
        marker.write_text(pin.sha256)
    else:
        fetch_wheel(pin, cache)  # re-verify the hash of the cached wheel on every run
    return env / "bin"


def install(pin: Pin, cache: Path) -> Path:
    """The pinned Vyper compiler; returns the `vyper` executable after checking its version."""
    exe = make_env(pin, cache, f"venv-{pin.version}") / "vyper"
    out = run([str(exe), "--version"]).strip()
    if not out.startswith(pin.version + "+commit."):
        sys.exit(f"{exe} reports version {out!r}, expected {pin.version}")
    return exe


def install_oracle(pin: Pin, cache: Path) -> Path:
    """The pinned py-evm; returns the interpreter of its environment after checking the version."""
    py = make_env(pin, cache, f"venv-pyevm-{pin.version}") / "python"
    out = run([str(py), "-c", "import eth; print(eth.__version__)"]).strip()
    if out != pin.version:
        sys.exit(f"py-evm reports version {out!r}, expected {pin.version}")
    return py


def run(cmd: list[str]) -> str:
    p = subprocess.run(cmd, capture_output=True, text=True)
    if p.returncode != 0:
        sys.exit(f"command failed ({p.returncode}): {' '.join(cmd)}\n{p.stderr}")
    return p.stdout


def compile_cell(exe: Path, src: Path, flags: list[str]) -> dict:
    base = [str(exe), "--evm-version", EVM_VERSION, *flags]
    runtime = run(base + ["-f", "bytecode_runtime", str(src)]).strip()
    abi = json.loads(run(base + ["--show-gas-estimates", "-f", "abi", str(src)]))
    ids = json.loads(run(base + ["-f", "method_identifiers", str(src)]))
    layout = json.loads(run(base + ["-f", "layout", str(src)]))
    if not runtime.startswith("0x") or not re.fullmatch(r"[0-9a-f]*", runtime[2:]):
        sys.exit(f"unexpected bytecode output for {src}: {runtime[:40]}")
    estimates = sorted((f["name"], int(f["gas"])) for f in abi
                       if f.get("type") == "function" and "gas" in f)
    selectors = sorted((sig, int(sel, 16)) for sig, sel in ids.items())
    slots = sorted((name, int(v["slot"])) for name, v in layout["storage_layout"].items())
    return {"runtime": runtime[2:], "estimates": estimates, "selectors": selectors,
            "slots": slots}


W = 2 ** 256


def word(n: int) -> str:
    return (n % W).to_bytes(32, "big").hex()


def oracle_points(contract: str, bound: int | None, selectors: list[tuple[str, int]]) -> list:
    """Calls replayed on py-evm: `(signature, args, x0, value)`. They mirror the domains of the
    business laws in `FixtureTests.lean` (§1), plus the ABI guards and the getters."""
    pts = []
    if contract == "loop_if":
        pts += [("f(uint256)", [n], x0, 0) for x0 in (0, W - 100) for n in range(bound + 3)]
    elif contract == "sum_squares":
        pts += [("run(uint256)", [n], 0, 0) for n in range(bound + 3)]
    elif contract == "store":
        pts += [(sig, [v], x0, 0) for sig in ("set(uint256)", "bump(uint256)")
                for x0 in (0, 9, W - 1) for v in (0, 1, 2 ** 255, W - 1)]
    else:
        sys.exit(f"no oracle domain for corpus contract {contract}")
    for sig, _ in selectors:
        args = [7] if "(uint256)" in sig else []
        pts.append((sig, args, 5, 1))
        if not args:
            pts.append((sig, [], 77, 0))
    return pts


def run_oracle(py: Path, code_hex: str, slot: int, selectors: list[tuple[str, int]],
               pts: list) -> list:
    sel = dict(selectors)
    req = {"code": code_hex, "slot": slot,
           "points": [{"data": f"{sel[sig]:08x}" + "".join(word(a) for a in args), "x0": x0,
                       "value": value} for sig, args, x0, value in pts]}
    p = subprocess.run([str(py), str(ORACLE)], input=json.dumps(req), capture_output=True,
                       text=True)
    if p.returncode != 0:
        sys.exit(f"py-evm oracle failed:\n{p.stderr}")
    res = json.loads(p.stdout)
    return [(sig, args, x0, value, ok, gas, after, out)
            for (sig, args, x0, value), (ok, gas, after, out) in zip(pts, res, strict=True)]


def loop_bound(text: str) -> str:
    bounds = [int(b) for b in re.findall(r"bound\s*=\s*(\d+)", text)]
    if len(bounds) > 1:
        sys.exit("a corpus contract may have at most one bounded loop")
    return f"some {bounds[0]}" if bounds else "none"


def lean_str(s: str) -> str:
    return '"' + s.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_pairs(xs: list[tuple[str, int]], hexa: bool = False) -> str:
    fmt = (lambda n: f"0x{n:08x}") if hexa else str
    return "[" + ", ".join(f"({lean_str(a)}, {fmt(b)})" for a, b in xs) + "]"


def generate(cache: Path) -> str:
    pins = read_lock()
    oracle_pin = read_lock(ORACLE_LOCK)[-1]
    py = install_oracle(oracle_pin, cache)
    sources = sorted(CORPUS.glob("*.vy"))
    if not sources:
        sys.exit("empty corpus")
    cells = []
    for pin in pins:
        exe = install(pin, cache)
        commit = run([str(exe), "--version"]).strip().split("+commit.")[1]
        for src in sources:
            text = src.read_text()
            for codegen, flags in CODEGENS:
                c = compile_cell(exe, src, flags)
                b = int(loop_bound(text).split()[1]) if loop_bound(text) != "none" else None
                slot = c["slots"][0][1]
                c["oracle"] = run_oracle(py, c["runtime"], slot, c["selectors"],
                                         oracle_points(src.stem, b, c["selectors"]))
                cells.append((pin, commit, src.stem, sha256_file(src), loop_bound(text),
                              codegen, c))
    lines = [
        "module",
        "",
        "public import EvmYul.Vyper.Fixture",
        "",
        "public section",
        "",
        "/-!",
        "# Vyper bytecode fixtures (generated; do not edit)",
        "",
        "Generated by `python3 tools/vyper/gen_vyper_fixtures.py` from `tools/vyper/corpus/*.vy` and",
        "the compilers pinned in `tools/vyper/vyper-matrix.lock` (wheel sha256 verified), all with",
        f"`--evm-version {EVM_VERSION}`. Each cell's `oracle` points were executed on py-evm (Cancun,",
        "`tools/vyper/oracle.lock`), an EVM implementation independent of this project.",
        "`lake run checkVyperFixtures` regenerates and diffs this file.",
        "The compiler output is an untrusted test input (`TCB.md`): it can make a test fail, never a",
        "theorem true.",
        "-/",
        "",
        "namespace EvmYul.Vyper",
        "",
        "/-- Every compiled cell: pinned compiler × corpus contract × code generator. -/",
        "@[expose] def fixtures : List Cell := [",
    ]
    body = []
    for pin, commit, name, src_sha, bound, codegen, c in cells:
        body.append("\n".join([
            "  { vyper := " + lean_str(pin.version) + ", commit := " + lean_str(commit) + ",",
            "    wheelSha256 := " + lean_str(pin.sha256) + ",",
            f"    codegen := .{codegen}, contract := {lean_str(name)},",
            "    sourceSha256 := " + lean_str(src_sha) + ",",
            f"    loopBound := {bound},",
            "    selectors := " + lean_pairs(c["selectors"], hexa=True) + ",",
            "    gasEstimates := " + lean_pairs(c["estimates"]) + ",",
            "    storageSlots := " + lean_pairs(c["slots"]) + ",",
            "    runtimeHex := " + lean_str(c["runtime"]) + ",",
            "    oracle := [" + ",\n      ".join(
                f"⟨{lean_str(sig)}, {args}, {x0}, {value}, {str(ok).lower()}, {gas}, {after}, "
                f"{lean_str(out)}⟩" for sig, args, x0, value, ok, gas, after, out in c["oracle"])
            + "] }",
        ]))
    lines.append(",\n".join(body) + " ]")
    lines += ["", "/-- The pinned latest compiler (last line of the lock file). -/",
              f"def pinnedLatest : String := {lean_str(pins[-1].version)}", "",
              "/-- The independent EVM that produced the `oracle` points (`tools/vyper/oracle.lock`). -/",
              f"def oracleVersion : String := {lean_str('py-evm ' + oracle_pin.version)}", "",
              "/-- sha256 of the verified py-evm wheel. -/",
              f"def oracleWheelSha256 : String := {lean_str(oracle_pin.sha256)}", "",
              "end EvmYul.Vyper", ""]
    return "\n".join(lines)


def latest_on_pypi() -> str:
    with urllib.request.urlopen("https://pypi.org/pypi/vyper/json") as r:
        return json.load(r)["info"]["version"]


def version_key(v: str) -> tuple[int, ...]:
    return tuple(int(x) for x in re.findall(r"\d+", v)[:3])


def newer_release(pinned: str, latest: str) -> bool:
    return version_key(latest) > version_key(pinned)


def self_test() -> int:
    """Offline checks of the pure helpers (run by `lake run checkVyperFixtures` first)."""
    cases = [
        (newer_release("0.4.3", "0.4.10"), True), (newer_release("0.4.3", "0.5.0"), True),
        (newer_release("0.4.3", "0.4.3"), False), (newer_release("0.4.3", "0.4.2"), False),
        (loop_bound("for i: uint256 in range(n, bound=50):"), "some 50"),
        (loop_bound("x: public(uint256)"), "none"),
        (lean_str('a"b\\c'), '"a\\"b\\\\c"'),
        (lean_pairs([("f()", 0x0c55699c)], hexa=True), '[("f()", 0x0c55699c)]'),
    ]
    bad = [i for i, (got, want) in enumerate(cases) if got != want]
    if bad:
        print(f"self-test failed on cases {bad}", file=sys.stderr)
        return 1
    print(f"self-test: {len(cases)} helper cases pass")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true")
    ap.add_argument("--no-latest", action="store_true")
    ap.add_argument("--self-test", action="store_true")
    ap.add_argument("--cache", type=Path,
                    default=Path(os.environ.get("XDG_CACHE_HOME", Path.home() / ".cache"))
                    / "evmyul-vyper")
    args = ap.parse_args()
    if args.self_test:
        return self_test()
    args.cache.mkdir(parents=True, exist_ok=True)
    text = generate(args.cache)
    if not args.check:
        OUT.write_text(text)
        print(f"wrote {OUT.relative_to(REPO)}")
        return 0
    status = 0
    if OUT.read_text() != text:
        print(f"DRIFT: {OUT.relative_to(REPO)} differs from a fresh generation; rerun the "
              "generator and review the diff", file=sys.stderr)
        status = 1
    else:
        print(f"{OUT.relative_to(REPO)} is up to date")
    if not args.no_latest:
        pinned, latest = read_lock()[-1].version, latest_on_pypi()
        if newer_release(pinned, latest):
            print(f"NEWER RELEASE: vyper {latest} on PyPI, pinned latest is {pinned}; add it to "
                  "the lock file and regenerate", file=sys.stderr)
            status = 1
        else:
            print(f"pinned latest {pinned} is the newest stable release ({latest})")
    return status


if __name__ == "__main__":
    sys.exit(main())
