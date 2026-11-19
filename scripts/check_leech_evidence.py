"""Check the saved Leech verification record against this checkout (does not rerun Lean)."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
record = json.loads((root / 'docs/leech-shortest-verification.json').read_text(encoding='utf-8'))

def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()

if record['status'] != 'PASS':
    raise SystemExit('The saved verification did not pass.')
for name, expected in record['normalized_source_sha256'].items():
    if digest(root / name) != expected:
        raise SystemExit(f'Source differs from the verified revision: {name}')
axioms = root / 'docs/leech-shortest-axioms.txt'
if digest(axioms) != record['axiom_output_sha256']:
    raise SystemExit('The saved axiom output differs from the verified output.')
targets = re.findall(r'^#print axioms (\S+)', (root / 'CheckAxioms.lean').read_text(encoding='utf-8'), re.M)
if len(targets) != record['checked_declarations'] or len(set(targets)) != len(targets):
    raise SystemExit('The axiom inventory does not match the saved verification.')
new = []
for name in ['LeechMinimal', 'LeechCodeCounts', 'LeechOctadCount', 'LeechSignVectors',
             'LeechFourCount', 'LeechOddCount', 'LeechOctadVectors', 'LeechKissing']:
    source = (root / (name + '.lean')).read_text(encoding='utf-8')
    namespace = re.search(r'^namespace (\S+)', source, re.M)[1]
    new.extend(namespace + '.' + item for item in re.findall(r'^theorem (\S+)', source, re.M))
if new != record['new_public_theorems'] or not set(new) <= set(targets):
    raise SystemExit('A new public theorem is missing from the verification inventory.')
result = subprocess.run([sys.executable, '-X', 'utf8', str(root / '.github/check_axioms.py'),
                         str(root / 'CheckAxioms.lean'), str(axioms)], check=False)
if result.returncode:
    raise SystemExit(result.returncode)
print(f'PASS: saved evidence matches the sources; {len(new)} new public theorems are audited.')
print('This checks the saved record. Run lake build and the axiom audit to recheck the proofs.')
