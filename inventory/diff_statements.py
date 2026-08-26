#!/usr/bin/env python3
"""Phase-2 check: the evidence file's REDUNDANT statements must match the
LeanQuantum originals verbatim (modulo whitespace).

For each theorem name in evidence/Redundant.lean, find the declaration of the
same base name in Quantumlib/ForMathlib/, extract both statements (text from
the declaration keyword to the first `:=` or `by` at top bracket level), and
compare after whitespace normalization.  Exit nonzero on any mismatch.
"""
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "vendor" / "LeanQuantum" / "Quantumlib" / "ForMathlib"
EV = ROOT / "evidence" / "Redundant.lean"


def extract(text: str, name: str):
    """Extract 'theorem <name> ... :' statement text up to := or by."""
    m = re.search(rf"^theorem {re.escape(name)}\b", text, re.M)
    if not m:
        return None
    rest = text[m.start():]
    # scan to first top-level := or ' by' outside brackets
    depth = 0
    i = 0
    while i < len(rest):
        c = rest[i]
        if c in "([{⟨":
            depth += 1
        elif c in ")]}⟩":
            depth -= 1
        elif depth == 0 and rest.startswith(":=", i):
            return rest[:i]
        elif depth == 0 and rest.startswith(" by", i) and not rest[:i].rstrip().endswith(":="):
            return rest[:i]
        i += 1
    return None


def norm(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


def main() -> int:
    src_text = "\n\n".join(p.read_text() for p in sorted(SRC.rglob("*.lean")))
    ev_text = EV.read_text()
    names = re.findall(r"^theorem ([A-Za-z_][^\s(]*)", ev_text, re.M)
    bad = 0
    for name in names:
        base = name.split(".")[-1]
        ours = extract(ev_text, name)
        theirs = extract(src_text, base)
        if theirs is None:
            print(f"MISSING IN SOURCE: {base}")
            bad += 1
            continue
        # normalize the leading 'theorem <name>' token away
        o = norm(re.sub(rf"^theorem {re.escape(name)}", "", norm(ours)))
        t = norm(re.sub(rf"^theorem {re.escape(base)}", "", norm(theirs)))
        if o == t:
            print(f"OK  {base}")
        else:
            print(f"DIFF {base}\n  evidence: {o}\n  source:   {t}")
            bad += 1
    print(f"{len(names)} compared, {bad} mismatches")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
