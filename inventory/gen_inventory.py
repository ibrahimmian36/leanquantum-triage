#!/usr/bin/env python3
"""Machine-generated inventory of every declaration in Quantumlib/ForMathlib/.

Scans the vendored LeanQuantum checkout for top-level declarations
(def, theorem, lemma, instance, abbrev, notation, infix/infixl/infixr,
scoped notation) and emits inventory.tsv with file, line, kind, name,
and the full statement text (up to the := or by that starts the proof/body,
or the whole line for notations).

Run from the repo root:  python3 inventory/gen_inventory.py
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "vendor" / "LeanQuantum" / "Quantumlib" / "ForMathlib"

DECL_RE = re.compile(
    r"^(?P<attrs>(?:@\[[^\]]*\]\s*)*)"
    r"(?P<scoped>scoped(?:\[[A-Za-z0-9_.]+\])?\s+)?"
    r"(?P<kind>def|theorem|lemma|instance|abbrev|notation|infixl|infixr|infix|structure|inductive|class)\b"
    r"(?P<rest>.*)$"
)
NAME_RE = re.compile(r"^\s*(?:\(priority[^)]*\)\s*)?(?P<name>[A-Za-z_][A-Za-z0-9_'.₀-₉ₐ-ₜ]*[!?]?)")


def statement_of(lines, i):
    """Collect declaration text from line i until the proof body starts
    (`:= by`, `:=`, `where`, or `by` at a delimiter) or until the next
    top-level declaration / blank-line boundary heuristic."""
    buf = []
    depth = 0
    for j in range(i, min(i + 40, len(lines))):
        line = lines[j]
        if j > i and DECL_RE.match(line):
            break
        buf.append(line.rstrip())
        text = " ".join(buf)
        # crude: stop once we hit := or ' by' outside brackets
        stripped = re.sub(r"\s+", " ", text)
        m = re.search(r":=|\bby\b", stripped)
        if m:
            return stripped[: m.start()].strip()
    return re.sub(r"\s+", " ", " ".join(buf)).strip()


def main():
    rows = []
    for f in sorted(SRC.rglob("*.lean")):
        rel = f.relative_to(ROOT / "vendor" / "LeanQuantum")
        lines = f.read_text().splitlines()
        namespace = []
        for i, line in enumerate(lines):
            ns_m = re.match(r"^namespace\s+([A-Za-z0-9_.]+)", line)
            if ns_m:
                namespace.append(ns_m.group(1))
                continue
            if re.match(r"^end\b", line) and namespace:
                namespace.pop()
                continue
            m = DECL_RE.match(line)
            if not m:
                continue
            kind = m.group("kind")
            rest = m.group("rest")
            if kind in ("notation", "infix", "infixl", "infixr"):
                name = rest.strip()
                stmt = line.strip()
            else:
                nm = NAME_RE.match(rest)
                name = nm.group("name") if nm else "<anonymous>"
                if ".".join(namespace) and not name.startswith("_root_"):
                    name = ".".join(namespace) + "." + name
                stmt = statement_of(lines, i)
            attrs = m.group("attrs").strip()
            scoped = (m.group("scoped") or "").strip()
            rows.append((str(rel), i + 1, (scoped + " " + kind).strip(), name, attrs, stmt))

    out = ROOT / "inventory" / "inventory.tsv"
    with out.open("w") as fh:
        fh.write("file\tline\tkind\tname\tattrs\tstatement\n")
        for r in rows:
            fh.write("\t".join(str(x) for x in r) + "\n")
    print(f"{len(rows)} declarations -> {out}")


if __name__ == "__main__":
    sys.exit(main())
