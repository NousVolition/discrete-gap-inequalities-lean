"""Check saved correspondence evidence and source hashes; does not rerun Lean."""
from pathlib import Path
import hashlib
import json
from datetime import datetime
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]

# Saved records are kept and never overwritten. The first record is
# docs/playground-golay-verification.json, and each later check adds a dated file
# docs/playground-golay-verification-YYYY-MM-DD.json. Every saved record must say PASS,
# and this checkout is compared against the newest one (latest verified_at_utc).
first = root / 'docs/playground-golay-verification.json'
paths = [first] + sorted((root / 'docs').glob('playground-golay-verification-*.json'))
records = [(json.loads(path.read_text(encoding='utf-8')), path) for path in paths]
for saved, path in records:
    assert saved.get('status') == 'PASS', f'A saved verification did not pass: {path.name}'
record, record_path = max(records, key=lambda item: datetime.fromisoformat(item[0]['verified_at_utc']))
# A later record must list the records before it, so none can be dropped without notice.
if record_path != first:
    previous = record.get('previous_records', [])
    assert 'docs/playground-golay-verification.json' in previous, \
        f'{record_path.name} does not list the first saved record.'
    for name in previous:
        assert (root / name).is_file(), f'A saved record listed by {record_path.name} is missing: {name}'
def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()

assert record['status'] == 'PASS'
for name, expected in record['normalized_source_sha256'].items():
    assert digest(root / name) == expected, f'Source differs: {name}'
# The first record has no axiom_output_file entry; it used docs/playground-golay-axioms.txt.
axioms = root / record.get('axiom_output_file', 'docs/playground-golay-axioms.txt')
assert digest(axioms) == record['axiom_output_sha256']
targets = re.findall(r'^#print axioms (\S+)', (root / 'CheckAxioms.lean').read_text(encoding='utf-8'), re.M)
assert len(targets) == len(set(targets)) == record['checked_declarations']
new = []
for module in ['PlaygroundGolay', 'PlaygroundLeech']:
    source = (root / (module + '.lean')).read_text(encoding='utf-8')
    new += [module + '.' + n for n in re.findall(r'^theorem (\S+)', source, re.M)]
assert new == record['new_public_theorems'] and set(new) <= set(targets)
subprocess.run([sys.executable, '-X', 'utf8', str(root / '.github/check_axioms.py'),
                str(root / 'CheckAxioms.lean'), str(axioms)], check=True)
replay = json.loads((root / 'docs/playground-golay-replay.json').read_text(encoding='utf-8-sig'))
assert replay['status'] == 'PASS'
for name, expected in replay['formal_source_sha256'].items():
    assert digest(root / name) == expected, f'Replay source differs: {name}'
assert digest(root / 'docs/playground-golay-source.js') == replay['source_slice_sha256']
print(f'PASS ({record_path.name}): saved sources, {len(new)} new theorems, complete axiom output and JavaScript replay hashes match.')
print('This checks recorded evidence. Rebuild Lean and rerun the Node script for fresh verification.')
