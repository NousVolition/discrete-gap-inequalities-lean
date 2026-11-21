"""Bind the 19 ring/store checks to their sources, target list and GitHub run."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SNAPSHOT = ROOT / 'research/wirtinger-store/local-check'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audit(source, output, targets):
    declared = ['WirtingerStore.' + name for name in
                re.findall(r'^theorem\s+(\w+)', source, re.M)]
    printed = re.findall(r'^#print axioms (\S+)', source, re.M)
    if len(targets) != 19 or len(set(targets)) != 19 or declared != targets or printed != targets:
        raise SystemExit('The 19-statement inventory does not match the saved check')
    reports = {}
    for line in output.splitlines():
        match = re.fullmatch(r"'([^']+)' depends on axioms: \[(.*)\]", line)
        if not match:
            raise SystemExit('Unexpected compiler or audit output')
        name, raw = match.groups()
        if name in reports:
            raise SystemExit('Duplicate axiom report: ' + name)
        used = [word.strip() for word in raw.split(',') if word.strip()]
        if set(used) - ALLOWED:
            raise SystemExit('Nonstandard axiom: ' + name)
        reports[name] = used
    if set(reports) != set(targets):
        raise SystemExit('Missing or unexpected axiom report')
    return reports


def main():
    historical = json.loads((SNAPSHOT / 'verification.json').read_text())
    conversion_path = SNAPSHOT.parent / 'source-inputs.json'
    conversion = json.loads(conversion_path.read_text())
    if conversion['local_receipt_sha256'] != sha(SNAPSHOT / 'verification.json'):
        raise SystemExit('Historical receipt changed')
    source = ROOT / 'WirtingerStore.lean'
    if sha(source) != historical['source_sha256'] or source.read_bytes() != (SNAPSHOT / source.name).read_bytes():
        raise SystemExit('Proof differs from the saved local check')
    for build in historical['builds']:
        path = ROOT / (build['module'] + '.lean')
        record = conversion['sources'][path.name]
        if record['compiled_local_sha256'] != build['source_sha256'] or sha(path) != record['published_sha256']:
            raise SystemExit('Proof input changed: ' + path.name)
        raw = path.read_bytes()
        blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
        if blob != record['repository_git_blob']:
            raise SystemExit('Repository blob differs: ' + path.name)
    log = ROOT / 'wirtinger-store-axioms.txt'
    axioms = audit(source.read_text(encoding='utf-8'), log.read_text(encoding='utf-8'), historical['targets'])
    saved_log = SNAPSHOT / 'axioms.log'
    if sha(saved_log) != historical['builds'][-1]['log_sha256']:
        raise SystemExit('Historical axiom log changed')
    if audit(source.read_text(encoding='utf-8'), saved_log.read_text(encoding='utf-8'), historical['targets']) != axioms:
        raise SystemExit('Axiom dependencies differ from the local check')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    mathlib = next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib')
    if mathlib != historical['mathlib_commit']:
        raise SystemExit('Mathlib revision differs from the local check')
    sources = set()
    pending = ['WirtingerStore.lean']
    while pending:
        name = pending.pop()
        if name in sources:
            continue
        sources.add(name)
        for line in (ROOT / name).read_text(encoding='utf-8').splitlines():
            if line.startswith('import '):
                for module in line[7:].split():
                    path = module.replace('.', '/') + '.lean'
                    if (ROOT / path).is_file():
                        pending.append(path)
    if sources != {b['module'] + '.lean' for b in historical['builds']}:
        raise SystemExit('Repository dependency closure differs from the local build')
    paths = sorted(sources | {'lakefile.toml', 'lake-manifest.json', 'lean-toolchain',
                   '.github/check_axioms.py', '.github/record_wirtinger_store_check.py',
                   '.github/workflows/wirtinger-store.yml', 'research/wirtinger-store/source-inputs.json'})
    inputs = {name: sha(ROOT / name) for name in paths}
    fingerprint = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    lean = subprocess.check_output(['lake', 'env', 'lean', '--version'], cwd=ROOT, text=True).strip()
    if '4.34.0-rc2' not in lean or '6a10ac8c22beadecabdbb0919c2b50214762f91d' not in lean:
        raise SystemExit('Unexpected Lean version')
    report = {
        'status': 'PASS', 'target_count': 19, 'targets': axioms,
        'source_commit': os.environ['GITHUB_SHA'],
        'run_id': os.environ['GITHUB_RUN_ID'],
        'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT', '1'),
        'run_url': os.environ['GITHUB_SERVER_URL'] + '/' + os.environ['GITHUB_REPOSITORY'] + '/actions/runs/' + os.environ['GITHUB_RUN_ID'],
        'lean_version': lean, 'mathlib_commit': mathlib,
        'proof_input_sha256': inputs, 'proof_input_fingerprint': fingerprint,
        'axiom_log_sha256': sha(log), 'local_receipt_sha256': sha(SNAPSHOT / 'verification.json'),
        'credit': historical['credit'],
        'scope': '19 general Lean statements about continuous heat on a finite ring, the no-input store bound and its sharp rate. No numerical gap or fluid simulation is checked by this job.'}
    (ROOT / 'wirtinger-store-lean-receipt.json').write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print('19 declarations checked, 0 nonstandard, 0 missing')


if __name__ == '__main__':
    main()
