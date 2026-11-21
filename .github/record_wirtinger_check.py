"""Bind the focused Lean audit to the checked sources and GitHub revision."""
from pathlib import Path
import hashlib
import json
import os
import re

root = Path(__file__).resolve().parents[1]
snapshot = root / 'research/riemann-wirtinger/local-check'
historical = json.loads((snapshot / 'verification.json').read_text())
sha256 = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for name, expected in historical['sources_and_records'].items():
    if sha256(snapshot / name) != expected:
        raise SystemExit('Historical receipt mismatch: ' + name)
modules = [b['source_file'] for b in historical['builds'] if b['module'] != 'CheckAxioms']
for name in modules:
    if (root / name).read_bytes() != (snapshot / name).read_bytes():
        raise SystemExit('Published proof differs from local checked source: ' + name)
targets = list(historical['axioms'])
inventory = re.findall(r'^#print axioms (\S+)', (root / 'CheckAxioms.lean').read_text(), re.M)
if len(targets) != 16 or any(inventory.count(t) != 1 for t in targets):
    raise SystemExit('Focused target inventory mismatch')
output = (root / 'axioms.txt').read_text()
reports = dict(re.findall(r"^'(.+)' depends on axioms: \[([^\]]*)\]", output, re.M))
axioms = {}
for target in targets:
    if target not in reports:
        raise SystemExit('Missing report: ' + target)
    used = [a.strip() for a in reports[target].split(',') if a.strip()]
    if set(used) - {'propext', 'Classical.choice', 'Quot.sound'}:
        raise SystemExit('Nonstandard axiom: ' + target)
    axioms[target] = used
paths = modules + ['CheckAxioms.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                    '.github/check_axioms.py', '.github/record_wirtinger_check.py', '.github/workflows/lean.yml']
inputs = {p: sha256(root / p) for p in paths}
fingerprint = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
report = {'status': 'PASS', 'target_count': len(targets), 'targets': axioms,
          'source_commit': os.environ['GITHUB_SHA'], 'run_id': os.environ['GITHUB_RUN_ID'],
          'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT', '1'),
          'run_url': os.environ['GITHUB_SERVER_URL'] + '/' + os.environ['GITHUB_REPOSITORY'] + '/actions/runs/' + os.environ['GITHUB_RUN_ID'],
          'proof_input_sha256': inputs, 'proof_input_fingerprint': fingerprint,
          'axiom_log_sha256': sha256(root / 'axioms.txt'), 'local_receipt_sha256': sha256(snapshot / 'verification.json'),
          'scope': '16 named Lean statements, including conditional RH implications. Numerical zeros and integrals are checked in a separate job. RH remains unproved.'}
out = root / 'wirtinger-lean-receipt.json'
out.write_text(json.dumps(report, indent=2) + '\n')
print('16 declarations checked, 0 nonstandard, 0 missing; RH remains unproved')
