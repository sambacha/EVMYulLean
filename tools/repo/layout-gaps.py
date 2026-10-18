#!/usr/bin/env python3
"""Report the fractal-layout rules of GUIDELINES.md §3, including what `Audits.Layout` (L1-L16) enforces.

    tools/repo/layout-gaps.py            # print the report
    tools/repo/layout-gaps.py --summary  # print only the counts

Read-only: it reads the tracked `.lean` files under `EvmYul/`, `Conform/`, `Audits/` and the
top-level indexes, and prints, per rule, the places that do not follow it. It never fails the build;
it is the measurement behind `docs/FRACTAL_LAYOUT_REMAINING.md`, so the figures there can be
re-derived. Rules that are build checks now (L9-L16) are mirrored here so that a failing build can be
explained without Lean; the counts of those rules must be 0 on a tree that builds. Classification (test-like, index file) follows `GUIDELINES.md` Rule 2 and
`Audits/LayoutModel.lean`.
"""
import collections
import functools
import os
import re
import subprocess
import sys

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
os.chdir(ROOT)

TOP = ("EvmYul", "Conform", "Audits")
TOP_FILES = ("EvmYul.lean", "Conform.lean", "Audits.lean", "EvmYulTests.lean", "ConformTests.lean")
SUFFIXES = ("Tests", "TestHarness", "Witnesses", "Lint")
EXCLUDED = ("EvmYul.Yul.SolidityYulInterpreterTests",)  # GUIDELINES.md §5.2
# Recorded exceptions of GUIDELINES.md §5.2, mirrored from `Audits/Layout.lean` (`cycleExempt`,
# `suiteRunners`). Rules 3 and 6 are build checks now (L10, L9); the script lists the recorded
# exceptions separately so that its counts show what is still open.
RECORDED_CYCLES = {("EvmYul.EVM", "EvmYul.Semantics"), ("EvmYul.Semantics", "EvmYul.Yul"),
                   ("EvmYul.EVM.Gas", "EvmYul.EVM.Semantics")}
RUNNERS = {"EvmYul.EVM.Gas.FFIBuildTests"}
# single-node folders recorded in GUIDELINES.md §5.2 (`singleNodeExempt` in Audits/Layout.lean, L11)
SINGLE_NODE_RECORDED = {"EvmYul.FFI"}

files = [f for f in subprocess.check_output(["git", "ls-files", "*.lean"], text=True).split()
         if f.split("/")[0] in TOP or f in TOP_FILES]


def mod(f):
    return f[:-5].replace("/", ".")


IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?(\S+)", re.M)
text = {mod(f): open(f, encoding="utf-8").read() for f in files}
imps = {m: sorted(set(IMPORT.findall(t))) for m, t in text.items()}
mods = set(imps)
folders = {".".join(m.split(".")[:i]) for m in mods for i in range(1, len(m.split(".")))}


def testlike(m):
    p = m.split(".")
    if p[0] == "Audits" or p[-1].endswith(SUFFIXES):
        return True
    return any(c == "Testing" or c.endswith(SUFFIXES) for c in p[:-1])


def isindex(m):
    return m in folders or (m.endswith("Tests") and m[:-5] in folders)


def ismain(m):
    return m.split(".")[-1].endswith("Main")


def excluded(m):
    return any(m == e or m.startswith(e + ".") for e in EXCLUDED)


@functools.lru_cache(None)
def reach(m):
    out = set()
    for i in imps.get(m, []):
        if i in mods and i not in out:
            out.add(i)
            out |= reach(i)
    return frozenset(out)


ordinary = sorted(m for m in mods if not isindex(m) and not excluded(m))
report = collections.OrderedDict()

# Rule 3: a test file that other test files import (shared fixtures belong in a test-support module)
r3 = []
for m in ordinary:
    if ismain(m):  # Rule 7: an entry point may call into test modules
        continue
    for i in imps[m]:
        if (i in mods and testlike(i) and not isindex(i) and i.split(".")[0] != "Audits"
                and not i.endswith("TestHarness") and ".Testing." not in "." + i + "."):
            r3.append((m, f"{m} imports test file {i}"))
report["Rule 3: test files imported as fixture libraries"] = [x for m, x in r3 if m not in RUNNERS]
report["Rule 3: recorded runners (GUIDELINES.md §5.2)"] = [x for m, x in r3 if m in RUNNERS]

# Rule 3: one subject, stated in the first `# ` heading
def subject_heading(t):
    """L12: the `# ` title on the first non-blank line of the first module docstring, else None."""
    parts = t.split("/-!", 1)
    if len(parts) < 2:
        return None
    lines = [l.strip() for l in parts[1].split("-/", 1)[0].split("\n") if l.strip()]
    if not lines or not lines[0].startswith("# ") or not lines[0][2:].strip():
        return None
    return lines[0][2:].strip()


report["Rule 3: modules without a `# ` subject heading (L12)"] = [
    m for m in ordinary if subject_heading(text[m]) is None]

# Rule 4: single-module folders
r4 = []
for d in sorted(folders):
    if excluded(d):
        continue
    kids = [m for m in mods if m.rsplit(".", 1)[0] == d] + \
           [x for x in folders if x.rsplit(".", 1)[0] == d and x != d]
    if len(kids) == 1:
        r4.append(f"{d} holds only {kids[0]}")
report["Rule 4: folders with a single file"] = [
    x for x in r4 if x.split(" ", 1)[0] not in SINGLE_NODE_RECORDED]
report["Rule 4: recorded single-file folders (GUIDELINES.md §5.2)"] = [
    x for x in r4 if x.split(" ", 1)[0] in SINGLE_NODE_RECORDED]

# Rule 5: a specific module of another node imported although its parent file would do
r5 = []
for m in ordinary:
    if ismain(m):
        continue
    mf = m.rsplit(".", 1)[0]
    for i in imps[m]:
        if i not in mods or isindex(i):
            continue
        f = i.rsplit(".", 1)[0]
        if f == mf or mf.startswith(f + ".") or f not in mods:
            continue
        cyc = m == f or m in reach(f)
        testdep = not testlike(m) and any(testlike(x) for x in reach(f))
        if not cyc and not testdep:
            r5.append(f"{m} imports {i} (parent file {f} is cycle-free here)")
report["Rule 5: imports from Conform/Audits that must use the parent file (L15)"] = [
    x for x in r5 if x.split(".", 1)[0] in ("Conform", "Audits") and not testlike(x.split(" ")[2])]
report["Rule 5: imports inside EvmYul that could use the parent file (a preference there)"] = [
    x for x in r5 if x.split(".", 1)[0] == "EvmYul"]


# Rule 6: sibling nodes that import each other (library modules only)
def child(m, parent):
    p = m.split(".")
    q = parent.split(".") if parent else []
    return ".".join(p[:len(q) + 1]) if p[:len(q)] == q and len(p) > len(q) else None


r6 = []
for parent in sorted(folders | {""}):
    edges = collections.defaultdict(list)
    for m in ordinary:
        if testlike(m):
            continue
        a = child(m, parent)
        for i in imps[m]:
            if i in mods and not testlike(i):
                b = child(i, parent)
                if a and b and a != b:
                    edges[(a, b)].append((m, i))
    for (a, b), ex in sorted(edges.items()):
        if a < b and (b, a) in edges and (a in folders or b in folders):
            back = edges[(b, a)][0]
            r6.append(((a, b), f"{a} <-> {b}: {ex[0][0]} -> {ex[0][1]}; {back[0]} -> {back[1]}"))
report["Rule 6: sibling nodes that import each other"] = [
    x for k, x in r6 if k not in RECORDED_CYCLES]
report["Rule 6: recorded cycles (GUIDELINES.md §5.2)"] = [x for k, x in r6 if k in RECORDED_CYCLES]

# Rule 8: XTests.lean whose subject X.lean (or folder X/) does not exist
report["Rule 8: test files without a same-named subject"] = [
    m for m in ordinary if m.endswith("Tests") and m[:-5] not in mods and m[:-5] not in folders]

# Rule 10: node-local documentation
r10 = []
for d in sorted(folders):
    if excluded(d):
        continue
    readme = d.replace(".", "/") + "/README.md"
    if not os.path.exists(readme):
        r10.append(f"{readme}: missing")
        continue
    body = open(readme, encoding="utf-8").read()
    lib = not testlike(d + ".X")
    kids = [m.rsplit(".", 1)[1] for m in ordinary
            if m.rsplit(".", 1)[0] == d and not ismain(m) and (not lib or not testlike(m))]
    kids += [x.rsplit(".", 1)[1] for x in folders if "." in x and x.rsplit(".", 1)[0] == d
             and any(o.startswith(x + ".") and (not lib or not testlike(o)) for o in ordinary)]
    missing = [k for k in kids if f"`{k}.lean`" not in body and f"`{k}/`" not in body]
    if missing:
        r10.append(f"{readme}: does not name {missing}")
report["Rule 10: folder READMEs missing or not naming every library child (L13)"] = r10

# Rule 10: living documentation names only existing Lean files (L14)
HISTORY = ("formerly", "previously", "was ", "were ", "old ", "renamed", "moved", "became", "→",
           "before", "used to", "no longer", "replaced")
lean_paths = [f[:-5].split("/") for f in subprocess.check_output(
    ["git", "ls-files", "*.lean"], text=True).split()]
docs = ["README.md", "GUIDELINES.md", "TESTING.md", "TCB.md"] + sorted(
    os.path.join(dp, f) for r in ("docs",) + TOP for dp, _, fs in os.walk(r) for f in fs
    if f.endswith(".md"))
r14 = []
for doc in docs:
    body = open(doc, encoding="utf-8").read()
    if any("<!-- historical log" in l for l in body.split("\n")[:5]):
        continue
    for n, line in enumerate(body.split("\n"), 1):
        if any(w in line.lower() for w in HISTORY):
            continue
        for t in line.split("`")[1::2]:
            if t.endswith(".lean") and "/" in t and not any(c in t for c in "*…{ <"):
                parts = [x for x in t.removeprefix("./")[:-5].split("/") if x]
                if not any(f[-len(parts):] == parts for f in lean_paths if len(f) >= len(parts)):
                    r14.append(f"{doc}:{n}: {t}")
report["Rule 10: stale Lean file references in living documentation (L14)"] = r14

# Visibility: blanket `@[expose] public section` in library modules
LEGACY_EXPOSED = set(re.findall(r'"([^"]+\.lean)"', open("Audits/Layout.lean", encoding="utf-8")
                                .read().split("def legacyExposed", 1)[1].split("]", 1)[0]))
# An `@[expose]` section header in any form Lean accepts (as `exposeSectionHeader?` in
# Audits/LayoutModel.lean): modifiers public/noncomputable/meta, an optional name, a trailing `--`
# comment, or the attribute alone on the line above.
def attribute_only(line):
    t, depth = line.strip(), 0
    if not t.startswith("@["):
        return False
    i = 0
    while i < len(t):
        c = t[i]
        if depth == 0:
            if c in " \t":
                pass
            elif t.startswith("@[", i):
                depth, i = 1, i + 1
            else:
                return False
        elif c == "[":
            depth += 1
        elif c == "]":
            depth -= 1
        i += 1
    return depth == 0
def join_attribute_lines(lines):
    out = []
    for line in lines:
        if out and attribute_only(out[-1]):
            out[-1] = out[-1].rstrip() + " " + line.strip()
        else:
            out.append(line)
    return out
def expose_header(line):
    ws = line.split("--", 1)[0].split()
    if not ws or ws[0] != "@[expose]":
        return None
    rest = ws[1:]
    mods = []
    while rest and rest[0] in ("public", "noncomputable", "meta"):
        mods.append(rest.pop(0))
    if rest[:1] == ["section"] and len(rest) <= 2:
        return mods, (rest[1] if len(rest) == 2 else "")
    return None
def blanket_expose(src):
    return any((h := expose_header(l)) and "public" in h[0] for l in join_attribute_lines(src.split("\n")))
exposed = [m for m in ordinary if not testlike(m) and not ismain(m) and m.split(".")[0] != "Audits"
           and blanket_expose(text[m])]
report["Visibility: new library modules with a blanket `@[expose] public section` (L16)"] = [
    m for m in exposed if m.replace(".", "/") + ".lean" not in LEGACY_EXPOSED]
report["Visibility: reviewed legacy modules that keep it (`legacyExposed`, shrink-only)"] = [
    m for m in exposed if m.replace(".", "/") + ".lean" in LEGACY_EXPOSED]

# Visibility, checked by L18: a local `@[expose] section` is closed and encloses exactly one top-level
# declaration (a `mutual` block counts once, and its `end` does not close the section)
DECL = ("def ", "abbrev ", "instance", "structure ", "inductive ", "class ", "opaque ", "mutual")
def strip_mods(l):
    l = l.strip()
    for _ in range(8):
        if l.startswith("@[") and "] " in l:
            l = l.split("] ", 1)[1].strip()
        for mod in ("private ", "protected ", "noncomputable ", "partial ", "unsafe ", "nonrec ", "meta "):
            if l.startswith(mod):
                l = l[len(mod):]
    return l
r18 = []
for m in ordinary:
    if testlike(m) or ismain(m) or m.split(".")[0] == "Audits":
        continue
    body = re.sub(r"/-.*?-/", "", text[m], flags=re.S)
    state = None  # None outside, else [count, in_mutual, name]
    for line in join_attribute_lines(body.split("\n")):
        t = line.strip()
        if state is None:
            h = expose_header(line)
            if h and "public" not in h[0]:
                state = [0, False, h[1]]
        elif state[1] and t == "end":
            state[1] = False
        elif t == ("end " + state[2] if state[2] else "end"):
            if state[0] != 1:
                r18.append(f"{m}: a local `@[expose] section` encloses {state[0]} declarations")
            state = None
        elif not line.startswith((" ", "\t")) and strip_mods(line).startswith(DECL):
            state[0] += 1
            state[1] = state[1] or strip_mods(line).startswith("mutual")
    if state is not None:
        r18.append(f"{m}: an unclosed local `@[expose] section`")
report["Visibility: local `@[expose] section`s that are unclosed or not around one declaration (L18)"] = r18

# Rule 1 (namespaces), checked by L17: a test-like namespace must end in the file's name, the test
# index name of its folder (`GasTests` in `.../Gas/`), or, in a harness `XTestHarness`, `XTests`
r1 = []
for m in ordinary:
    parts = m.split(".")
    base, folder = parts[-1], (parts[-2] if len(parts) > 1 else "")
    allowed = {base, folder + "Tests"}
    if base.endswith("TestHarness"):
        allowed.add(base[: -len("TestHarness")] + "Tests")
    code = re.sub(r"/-.*?-/", "", text[m], flags=re.S)
    for ns in re.findall(r"^\s*namespace\s+(\S+)", code, re.M):
        last = ns.split(".")[-1]
        if last.endswith(("Tests", "Witnesses", "Audit", "Lint")) and last not in allowed:
            r1.append(f"{m}: namespace {ns}")
report["Rule 1: test/audit namespaces not named after their file or folder (L17)"] = r1

summary = "--summary" in sys.argv
for title, items in report.items():
    print(f"{title}: {len(items)}")
    if not summary:
        for it in items:
            print(f"  {it}")
print(f"(scanned {len(files)} files, {len(ordinary)} ordinary modules, {len(folders)} folders)")
