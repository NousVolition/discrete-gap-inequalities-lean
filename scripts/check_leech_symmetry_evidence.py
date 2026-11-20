"""Compare saved symmetry-proof evidence with this checkout; does not run Lean."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
records = [json.loads(p.read_text(encoding='utf-8')) for p in (root/'docs').glob('leech-symmetry-verification*.json')]
record = max(records, key=lambda r: r['verified_at_utc'])
assert record['status'] == 'PASS'

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
for module in record.get('theorem_modules', ['LeechSymmetry', 'LeechMonomial', 'LeechFrameStabilizer']):
    source = (root / (module + '.lean')).read_text(encoding='utf-8')
    namespace = re.search(r'^namespace (\S+)', source, re.M)[1]
    names.extend(namespace + '.' + n for n in re.findall(r'^theorem (\w+)', source, re.M))
assert names == record['new_public_theorems']
assert set(names) <= set(targets), 'A new theorem is missing from the audit'
milestones = {
    'ConwayMoves.norm64_transitive': 'norm64_transitivity',
    'ConwayOrder.card_aut': 'full_conway_classification',
}
for theorem, field in milestones.items():
    assert record[field] == ('PROVED' if theorem in names else 'UNPROVED')
if record['full_conway_classification'] == 'PROVED':
    assert 'ConwayGenerators.listed_generate' in names
    assert record['full_group_order'] == '8315553613086720000'
    source = (root / 'ConwayOrder.lean').read_text(encoding='utf-8')
    assert re.search(r'^theorem card_aut\s*:\s*Nat\.card LeechSymmetry\.Aut\s*=\s*8315553613086720000\s*:=', source, re.M)
subprocess.run([sys.executable, str(root / '.github/check_axioms.py'),
                str(root / 'CheckAxioms.lean'), str(axioms)], check=True)
print(f'PASS: saved evidence matches {len(names)} symmetry theorems and {len(record["preserved_source_sha256"])} unchanged existing proof files.')
print('Co0 order proof:', record['full_conway_classification'], '(saved evidence).')
