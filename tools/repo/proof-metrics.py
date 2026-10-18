#!/usr/bin/env python3
"""Approximate proof-size metrics for Lean files (used by docs/PROOF_GOLF_REPORT.md).

For every `theorem` / `lemma` (and `instance` / `def` whose body is a tactic block) the script
finds the proof text after `:=` up to the next top-level command and reports

* tactic steps: non-blank, non-comment proof lines, plus one per extra `;` / `<;>` separator on a
  line (so `simp; omega` counts as 2), and 1 for a term-mode proof;
* proof lines: non-blank, non-comment lines of the proof text.

It is a heuristic (it does not parse Lean), but it is applied identically before and after, so the
differences are meaningful.

Usage: proof-metrics.py [--decls] FILE...
"""
import re
import sys

TOP = re.compile(
    r"^(@\[.*\]\s*)?(private |protected |noncomputable |public |nonrec |partial |unsafe )*"
    r"(theorem|lemma|def|abbrev|instance|example|structure|inductive|class|namespace|end|section|"
    r"open|variable|set_option|attribute|#|/-|--|universe|omit|include|mutual|noncomputable section|"
    r"public section|macro|syntax|elab|notation|scoped|local|initialize|deriving|@\[)"
)
PROOF_DECL = re.compile(
    r"^(@\[[^\]]*\]\s*)?(private |protected |public |nonrec )*(theorem|lemma)\s+([^\s(:{\[]+)"
)


def strip_comments(text):
    text = re.sub(r"/-.*?-/", lambda m: "\n" * m.group(0).count("\n"), text, flags=re.S)
    return "\n".join(re.sub(r"--.*$", "", l) for l in text.split("\n"))


def decls(path):
    raw = open(path, encoding="utf-8").read()
    lines = strip_comments(raw).split("\n")
    out = []
    i = 0
    n = len(lines)
    while i < n:
        m = PROOF_DECL.match(lines[i])
        if not m:
            i += 1
            continue
        name = m.group(4)
        j = i + 1
        while j < n and not (lines[j] and not lines[j][0].isspace() and TOP.match(lines[j])):
            j += 1
        body = "\n".join(lines[i:j])
        # The proof starts at the first `:=`, or at the first equation-compiler line `  | …`
        # for proofs by pattern matching (whichever comes first).
        k = body.find(":=")
        m2 = re.search(r"\n\s+\|", body)
        if m2 and (k < 0 or m2.start() < k):
            proof = body[m2.start():]
        else:
            proof = body[k + 2:] if k >= 0 else ""
        plines = [l for l in proof.split("\n") if l.strip()]
        if proof.strip().startswith("by") or re.search(r"\bby\b", proof):
            steps = 0
            for l in plines:
                s = l.strip()
                if s in ("by",):
                    continue
                s = re.sub(r"^by\s+", "", s)
                if not s:
                    continue
                steps += 1 + s.count("<;>") + len(re.findall(r";(?!>)", s.replace("<;>", "")))
        else:
            steps = 1
        out.append((name, max(steps, 1), len(plines)))
        i = j
    return out


def main():
    args = sys.argv[1:]
    show = False
    if args and args[0] == "--decls":
        show = True
        args = args[1:]
    ts = tl = td = 0
    for f in args:
        ds = decls(f)
        s = sum(d[1] for d in ds)
        l = sum(d[2] for d in ds)
        ts += s
        tl += l
        td += len(ds)
        print(f"{f}\t{len(ds)}\t{s}\t{l}")
        if show:
            for d in ds:
                print(f"    {d[0]}\t{d[1]}\t{d[2]}")
    print(f"TOTAL\t{td}\t{ts}\t{tl}")


if __name__ == "__main__":
    main()
