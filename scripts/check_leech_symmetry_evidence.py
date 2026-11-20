"""Compare saved symmetry-proof evidence with this checkout; does not run Lean."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
record = json.loads((root / 'docs/leech-symmetry-verification.json').read_text(encoding='utf-8'))
assert record['status'] == 'PASS'
assert record['full_conway_classification'] == 'UNPROVED'
assert record['norm64_transitivity'] == 'UNPROVED'

def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()

for name, expected in record['normalized_source_sha256'].items():
    assert digest(root / name) == expected, 'Source differs from saved verification: ' + name
for name, expected in record['preserved_source_sha256'].items():
    assert digest(root / name) == expected, 'Existing proof source changed: ' + name
axioms = root / record['axiom_output_file']
assert digest(axioms) == record['axiom_output_sha256'], 'Axiom output changed'
targets = re.findall(r'^#print axioms (\S+)', (root / 'CheckAxioms.lean').read_text(encoding='utf-8'), re.M)
assert len(targets) == len(set(targets)) == record['checked_declarations']
names = []
for module in ['LeechSymmetry', 'LeechMonomial', 'LeechFrameStabilizer']:
    source = (root / (module + '.lean')).read_text(encoding='utf-8')
    names.extend('LeechSymmetry.' + n for n in re.findall(r'^theorem (\w+)', source, re.M))
assert names == record['new_public_theorems']
assert set(names) <= set(targets), 'A new theorem is missing from the audit'
subprocess.run([sys.executable, str(root / '.github/check_axioms.py'),
                str(root / 'CheckAxioms.lean'), str(axioms)], check=True)
print(f'PASS: saved evidence matches {len(names)} symmetry theorems and {len(record["preserved_source_sha256"])} unchanged existing proof files.')
print('Full Co0 classification and norm-64 transitivity remain unproved. This command does not rerun Lean.')
