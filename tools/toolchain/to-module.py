#!/usr/bin/env python3
"""Convert Lean source files to the Lean 4.28 module system, in place.

    tools/toolchain/to-module.py FILE...

For each file that does not already start with `module`:

* `module` is inserted before the first `import` (after any leading comments), or as the first line
  if the file has no imports (its leading comment may then be the module docstring);
* every header `import X` becomes `public import X`;
* `@[expose] public section` is inserted after the header, so every declaration keeps the
  visibility it had before the conversion (public, with its body available to `rfl`/`decide`/`simp`
  in importing modules).

Idempotent: a file whose header already contains `module` is left unchanged.
"""
import sys


def scan_header(lines):
    """`(end, imports, has_module)`: the index of the first line after the header (comments, blank
    lines, imports), the indices of the header's `import` lines, and whether it already has `module`.
    Lines inside block comments are neither imports nor `module`, even if they look like one."""
    in_block = 0
    imports, has_module = [], False
    for i, line in enumerate(lines):
        s = line.strip()
        if in_block:
            in_block += s.count("/-") - s.count("-/")
            continue
        if s == "" or s.startswith("--"):
            continue
        if s.startswith("/-"):
            in_block = s.count("/-") - s.count("-/")
            continue
        if s.startswith("import "):
            imports.append(i)
            continue
        if s == "module" or s.startswith("public import "):
            has_module = True
            continue
        return i, imports, has_module
    return len(lines), imports, has_module


def convert(text):
    lines = text.split("\n")
    end, imports, has_module = scan_header(lines)
    head = lines[:end]
    if has_module:
        return text
    if not imports:
        # No imports (the file sees only `Init`): the header is just comments, which may include the
        # module docstring `/-! ... -/`, so `module` goes first and the docstring stays in the body.
        return "\n".join(["module", "", "@[expose] public section", ""] + lines)
    first, last = imports[0], imports[-1]
    pre = head[:first]
    while pre and pre[-1].strip() == "":
        pre.pop()
    out = pre + ([""] if pre else []) + ["module", ""]
    out += ["public " + l.strip() if i in imports else l for i, l in enumerate(head[first:last + 1], first)]
    out += ["", "@[expose] public section"] + head[last + 1:]
    return "\n".join(out + lines[end:])


if __name__ == "__main__":
    for path in sys.argv[1:]:
        with open(path, encoding="utf-8") as fh:
            src = fh.read()
        new = convert(src)
        if new != src:
            with open(path, "w", encoding="utf-8") as fh:
                fh.write(new)
