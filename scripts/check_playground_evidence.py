"""Check saved correspondence evidence and source hashes; does not rerun Lean."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
record = json.loads((root / 'docs/playground-golay-verification.json').read_text(encoding='utf-8'))
def digest(path):
    return hashlib.sha256(path.read_bytes().replace(b'\r\n', b'\n')).hexdigest()

assert record['status'] == 'PASS'
for name, expected in record['normalized_source_sha256'].items():
    assert digest(root / name) == expected, f'Source differs: {name}'
axioms = root / 'docs/playground-golay-axioms.txt'
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
print(f'PASS: saved sources, {len(new)} new theorems, complete axiom output and JavaScript replay hashes match.')
print('This checks recorded evidence. Rebuild Lean and rerun the Node script for fresh verification.')
