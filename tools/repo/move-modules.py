#!/usr/bin/env python3
"""Move Lean modules (and plain directories) and rewrite every reference to them.

    tools/repo/move-modules.py MAPPING [--dry-run]

MAPPING is a text file with one move per line (``#`` comments and blank lines ignored):

    module Old.Module.Name  New.Module.Name     # a Lean module: Old/Module/Name.lean
    dir    old/dir/path     new/dir/path        # a non-Lean directory (e.g. Python helpers)

For every move the file is moved with ``git mv`` and every tracked text file is rewritten:

* paths      ``Old/Module/Name.lean`` -> ``New/Module/Name.lean`` and ``old/dir/path`` -> ``new/dir/path``
             (everywhere: Lean, Markdown, shell, Python, the lakefile, ``.gitignore``);
* imports    ``import Old.Module.Name`` -> ``import New.Module.Name`` (with ``public``/``meta`` prefixes);
* name literals in Lean, single back-tick only: ``\u0060Old.Module.Name`` -> ``\u0060New.Module.Name``
             (module lists of audits, lakefile roots). Double back-tick ``\u0060\u0060Decl`` literals name
             *declarations* and are never touched: a move does not rename declarations;
* prose      in Markdown and in Lean comments the dotted module name is rewritten when it is not
             followed by ``.ident`` (so a declaration ``Old.Module.Name.foo`` is left alone);
* basenames  a quoted or back-ticked bare ``OldBase.lean`` becomes ``NewDir/NewBase.lean`` when the
             basename changed (``"GasMeter.lean"`` -> ``"Gas/Meter.lean"``), so suffix checks keep working.

All replacements of one run are applied simultaneously (one regex alternation, longest match first),
so a chain ``A -> B, B -> C`` cannot rewrite ``A`` to ``C``. Namespaces (``namespace``/``open``/``end``
lines) are never rewritten. Exit status 1 if a source is missing or a target exists.

Use together with ``tools/repo/DeclInventory.lean``: the declaration inventory must be identical
before and after a pure move.
"""
import os
import re
import subprocess
import sys

TEXT_EXT = {".lean", ".md", ".sh", ".py", ".txt", ".nix", ".toml", ".gitignore", ".lock", ".yml",
            ".yaml", ".json", ".cfg"}

# Session records and the input documents the project started from: kept verbatim (they describe
# the tree as it was at the time).
FROZEN = {"ARISTOTLE_SUMMARY.md", "EVMYulLean_Gas_Analysis.md", "EVMYulLean_Gas_Handoff.md"}


def tracked_files():
    out = subprocess.run(["git", "ls-files", "-z"], check=True, capture_output=True).stdout
    files = [f for f in out.decode().split("\0") if f]
    return [f for f in files if f not in FROZEN and
            (os.path.splitext(f)[1] in TEXT_EXT or os.path.basename(f) == ".gitignore")]


def mod_path(m):
    return m.replace(".", "/") + ".lean"


def parse(mapping):
    mods, dirs = [], []
    for raw in open(mapping):
        line = raw.split("#", 1)[0].strip()
        if not line:
            continue
        kind, old, new = line.split()
        (mods if kind == "module" else dirs).append((old, new))
    return mods, dirs


def rewrite_non_code(text, f):
    """Apply `f` to the comment and string-literal regions of Lean source `text` only."""
    out, i, n, depth = [], 0, len(text), 0
    code_start = 0
    while i < n:
        c, d = text[i], text[i + 1] if i + 1 < n else ""
        if c == "/" and d == "-":
            out.append(text[code_start:i])
            j, depth = i + 2, 1
            while j < n and depth:
                if text.startswith("/-", j):
                    depth += 1; j += 2
                elif text.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            out.append(f(text[i:j])); i = code_start = j
        elif c == "-" and d == "-":
            out.append(text[code_start:i])
            j = text.find("\n", i)
            j = n if j < 0 else j
            out.append(f(text[i:j])); i = code_start = j
        elif c == '"' and (i == 0 or text[i - 1] != "'"):
            out.append(text[code_start:i])
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == "\\" else 1
            j = min(j + 1, n)
            out.append(f(text[i:j])); i = code_start = j
        else:
            i += 1
    out.append(text[code_start:])
    return "".join(out)


def build_rewriter(mods, dirs):
    path_map = {mod_path(o): mod_path(n) for o, n in mods}
    path_map.update({o: n for o, n in dirs})
    name_map = dict(mods)
    base_map = {}
    for o, n in mods:
        ob, nb = o.split(".")[-1], n.split(".")[-1]
        if ob != nb:
            base_map[ob + ".lean"] = n.split(".")[-2] + "/" + nb + ".lean"

    def alt(keys):
        return "|".join(re.escape(k) for k in sorted(keys, key=len, reverse=True))

    path_re = re.compile(r"(?<![\w/])(" + alt(path_map) + r")(?![\w])") if path_map else None
    imp_re = re.compile(r"^((?:public |meta |private )*import\s+)(" + alt(name_map) + r")\s*$",
                        re.M) if name_map else None
    lit_re = re.compile(r"(?<![`\w.])`(" + alt(name_map) + r")(?![\w']|\.[\w])") if name_map else None
    prose_re = re.compile(r"(?<![\w.`])(" + alt(name_map) + r")(?![\w']|\.[\w])") if name_map else None
    base_re = re.compile(r"(?<=[\"`])(" + alt(base_map) + r")(?=[\"`])") if base_map else None

    def rewrite(path, text):
        if path_re:
            text = path_re.sub(lambda m: path_map[m.group(1)], text)
        if base_re:
            text = base_re.sub(lambda m: base_map[m.group(1)], text)
        if path.endswith(".lean"):
            if imp_re:
                text = imp_re.sub(lambda m: m.group(1) + name_map[m.group(2)], text)
            if lit_re:
                text = lit_re.sub(lambda m: "`" + name_map[m.group(1)], text)
            # prose: only inside comments and string literals, never in code
            if prose_re:
                text = rewrite_non_code(text, lambda t: prose_re.sub(
                    lambda m: name_map[m.group(1)], t))
        elif prose_re:
            text = prose_re.sub(lambda m: name_map[m.group(1)], text)
        return text

    return path_map, rewrite


def main():
    if len(sys.argv) < 2:
        print(__doc__)
        return 1
    dry = "--dry-run" in sys.argv
    mods, dirs = parse(sys.argv[1])
    path_map, rewrite = build_rewriter(mods, dirs)
    for old, new in path_map.items():
        if not os.path.exists(old):
            print(f"move: missing source {old}", file=sys.stderr)
            return 1
        if os.path.exists(new):
            print(f"move: target exists {new}", file=sys.stderr)
            return 1
    changed = 0
    for f in tracked_files():
        if not os.path.isfile(f):
            continue
        try:
            text = open(f, encoding="utf-8").read()
        except UnicodeDecodeError:
            continue
        new = rewrite(f, text)
        if new != text:
            changed += 1
            if not dry:
                open(f, "w", encoding="utf-8").write(new)
    for old, new in path_map.items():
        if dry:
            print(f"git mv {old} {new}")
            continue
        os.makedirs(os.path.dirname(new) or ".", exist_ok=True)
        subprocess.run(["git", "mv", old, new], check=True)
    print(f"move: {len(path_map)} path(s) moved, {changed} file(s) rewritten")
    return 0


if __name__ == "__main__":
    sys.exit(main())
