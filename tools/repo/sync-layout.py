#!/usr/bin/env python3
"""Keep every folder's parent file and test index in step with the folder (GUIDELINES.md §3).

    tools/repo/sync-layout.py --check     # exit 1 and list every difference (CI, reviews)
    tools/repo/sync-layout.py --write     # rewrite the import blocks; create missing files

The rules (the Lean audit `Audits.Layout` checks the same rules independently at build time):

* Source roots are the folders `EvmYul/`, `Conform/` and `Audits/`; the parent file of a folder
  `F/` is `F.lean` next to it (so `EvmYul.lean` is the parent of `EvmYul/`).
* A module is *test-like* when its file name ends in `Tests`, `TestHarness`, `Witnesses` or `Lint`,
  or when it lies in a folder whose name ends in one of those suffixes or is `Testing`, or under
  `Audits/` (a folder named like a test module is a test folder, so the parent-file rule and the
  library/test separation classify it the same way).
  A module whose name ends in `Main` is an executable entry point (a `lean_exe` root) and is imported
  by neither a parent file nor a test index.
* The parent file `F.lean` of a library folder imports exactly the library modules directly in `F/`
  and the parent file of every library subfolder (one that holds a library module somewhere below).
* The test index `FTests.lean` of a library folder imports exactly the test-like modules directly in
  `F/`, the test index of every library subfolder with tests, and the parent file of every test-like
  subfolder (e.g. `EvmYul/Testing.lean`). It exists iff there is something to import.
* A test-like folder (e.g. `Testing/`, `Audits/`) has only a parent file, which imports everything in it.
* Parent files and test indexes hold imports and a module docstring, never declarations. They are
  modules (`public import`), except under `Audits/`, whose files cannot be modules (`legacySources`
  in `EvmYul/Toolchain.lean`).

Folders listed in EXCLUDED are skipped, with the reason recorded next to them.
"""
import os
import re
import sys

ROOTS = ["EvmYul", "Conform", "Audits"]
TEST_ROOTS = {"Audits"}
EXCLUDED = {
    # Imports `GeneratedEvmYul` modules, generated from the pinned solidity corpus and not checked
    # in; built only with `lake -Kgenerated=on` (TESTING.md 0.2).
    "EvmYul/Yul/SolidityYulInterpreterTests",
}
TEST_SUFFIXES = ("Tests", "TestHarness", "Witnesses", "Lint")


def is_entry(mod_base):
    return mod_base.endswith("Main")


def is_test_folder(path):
    parts = path.split("/")
    return parts[0] in TEST_ROOTS or any(p.endswith(TEST_SUFFIXES) or p == "Testing" for p in parts)


def is_test_module(path):
    base = os.path.basename(path)[:-5]
    return is_test_folder(os.path.dirname(path)) or base.endswith(TEST_SUFFIXES)


def modname(path):
    return path[:-5].replace("/", ".")


def lean_children(folder):
    files, dirs = [], []
    for e in sorted(os.listdir(folder)):
        p = f"{folder}/{e}"
        if os.path.isdir(p):
            if p not in EXCLUDED and e != "__pycache__":
                dirs.append(p)
        elif e.endswith(".lean"):
            # a parent file `X.lean` of a sibling folder `X/` is handled with the folder
            files.append(p)
    return files, dirs


def own_modules(folder):
    """Importable modules directly in `folder` (no parent files / indexes of subfolders, no `Main`)."""
    files, dirs = lean_children(folder)
    skip = {d + ".lean" for d in dirs} | {d + "Tests.lean" for d in dirs}
    return [f for f in files if f not in skip and not is_entry(os.path.basename(f)[:-5])]


def has_lib(folder):
    """Does `folder` hold a library module, here or in a library subfolder?"""
    if is_test_folder(folder):
        return False
    _, dirs = lean_children(folder)
    return any(not is_test_module(f) for f in own_modules(folder)) or any(has_lib(d) for d in dirs)


def has_tests(folder):
    """Does `folder` hold a test-like module anywhere below it?"""
    _, dirs = lean_children(folder)
    return any(is_test_module(f) for f in own_modules(folder)) or any(has_tests(d) for d in dirs)


def expected(folder):
    """{file: [imports]} for the parent file and test index of `folder` (recursively)."""
    out = {}
    _, dirs = lean_children(folder)
    lib, tests = [], []
    for f in own_modules(folder):
        (tests if is_test_module(f) else lib).append(modname(f))
    for d in dirs:
        if is_test_folder(d):
            if has_tests(d):
                tests.append(modname(d + ".lean"))
        else:
            if has_lib(d):
                lib.append(modname(d + ".lean"))
            if has_tests(d):
                tests.append(modname(d + "Tests.lean"))
        out.update(expected(d))
    if is_test_folder(folder):
        if lib or tests:
            out[folder + ".lean"] = sorted(lib + tests)
    else:
        if lib:
            out[folder + ".lean"] = sorted(lib)
        if tests:
            out[folder + "Tests.lean"] = sorted(tests)
    return out


IMPORT_RE = re.compile(r"^(?:public |meta |private )*import\s+(\S+)\s*$", re.M)


def current_imports(path):
    if not os.path.exists(path):
        return None
    return sorted(IMPORT_RE.findall(open(path).read()))


def render(path, imports, old):
    is_index = path.endswith("Tests.lean") or is_test_folder(path[:-5])
    node = path[:-5]
    if old is not None:
        # keep everything after the import block (the docstring)
        lines = old.split("\n")
        last = max(i for i, l in enumerate(lines) if IMPORT_RE.match(l) or l.strip() == "module")
        rest = "\n".join(lines[last + 1:]).lstrip("\n")
    elif is_index:
        # `FTests.lean` indexes folder `F/`, unless `FTests/` is itself a (test) folder
        title = node[:-5] if node.endswith("Tests") and not os.path.isdir(node) else node
        rest = (f"/-!\n# Test index of `{title}/`\n\n"
                "Imports every test module of this folder and the test index of every subfolder\n"
                "(`GUIDELINES.md` §3, kept in step by `tools/repo/sync-layout.py`, checked by\n"
                "`Audits.Layout`). Holds no declarations.\n-/\n")
    else:
        rest = (f"/-!\n# `{modname(path)}`\n\n"
                f"Parent file of `{node}/`: imports the folder's modules and the parent file of\n"
                "each subfolder (`GUIDELINES.md` §3, kept in step by `tools/repo/sync-layout.py`,\n"
                "checked by `Audits.Layout`). Holds no declarations.\n-/\n")
    if path.split("/")[0].removesuffix(".lean") in TEST_ROOTS:
        # the audits are not modules (they read imported proofs), so neither is their index
        head = "".join(f"import {m}\n" for m in imports)
    else:
        head = "module\n\n" + "".join(f"public import {m}\n" for m in imports)
    return head + "\n" + rest


def main():
    write = "--write" in sys.argv
    if not write and "--check" not in sys.argv:
        print(__doc__)
        return 2
    want = {}
    for r in ROOTS:
        if os.path.isdir(r):
            want.update(expected(r))
    diffs = 0
    for path, imports in sorted(want.items()):
        cur = current_imports(path)
        if cur == imports:
            continue
        diffs += 1
        if cur is None:
            print(f"missing: {path}")
        else:
            print(f"{path}: +{sorted(set(imports) - set(cur))} -{sorted(set(cur) - set(imports))}")
        if write:
            old = open(path).read() if os.path.exists(path) else None
            open(path, "w").write(render(path, imports, old))
    print(f"sync-layout: {len(want)} parent files / test indexes, {diffs} out of step"
          + (" (rewritten)" if write and diffs else ""))
    return 1 if diffs and not write else 0


if __name__ == "__main__":
    sys.exit(main())
