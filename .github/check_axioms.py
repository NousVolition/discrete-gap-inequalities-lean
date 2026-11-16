"""Fail unless every `#print axioms` in CheckAxioms.lean reports only the standard axioms."""
import re, sys
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
src, out = open(sys.argv[1]).read(), open(sys.argv[2]).read()
wanted = re.findall(r"^#print axioms (\S+)", src, re.M)
seen, bad = set(), []
for name, axs in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out):
    seen.add(name)
    extra = {a.strip() for a in axs.split(",") if a.strip()} - ALLOWED
    if extra: bad.append(f"{name}: {sorted(extra)}")
seen |= set(re.findall(r"'([^']+)' does not depend on any axioms", out))
missing = [w for w in wanted if w not in seen]
for line in bad: print("NONSTANDARD AXIOM", line)
for m in missing: print("NO AXIOM REPORT", m)
print(f"{len(wanted)} declarations checked, {len(bad)} nonstandard, {len(missing)} missing")
sys.exit(1 if bad or missing or not wanted else 0)
