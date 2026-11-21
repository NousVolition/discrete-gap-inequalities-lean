"""Rerun the registered five-gap diagnostic without changing its saved results."""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
import sys
from decimal import Decimal, localcontext

root = Path(__file__).resolve().parents[1]
source = root / 'research/riemann-wirtinger/local-check'
work = Path(os.environ['RUNNER_TEMP']) / 'wirtinger-gap-replay'
work.mkdir(parents=True, exist_ok=False)
for name in ('study_gaps.py', 'gap-study-protocol.json'):
    shutil.copyfile(source / name, work / name)
subprocess.run([sys.executable, str(work / 'study_gaps.py')], check=True)
saved = json.loads((source / 'gap-study-results.json').read_text())
fresh = json.loads((work / 'gap-study-results.json').read_text())
protocol = json.loads((source / 'gap-study-protocol.json').read_text())
assert fresh['numerical_status'] == saved['numerical_status'] == 'PASS'
assert fresh['checks'] == saved['checks']
assert fresh['protocol_sha256'] == saved['protocol_sha256']
assert fresh['script_sha256'] == saved['script_sha256']
assert fresh['mpmath_version'] == saved['mpmath_version'] == '1.3.0'
largest = Decimal(0)
with localcontext() as ctx:
    ctx.prec = 70
    for expected, actual in zip(saved['passes'], fresh['passes'], strict=True):
        assert actual['decimal_precision'] == expected['decimal_precision']
        assert actual['subintervals'] == expected['subintervals']
        assert len(actual['rows']) == len(protocol['pairs']) == 5
        for old, new in zip(expected['rows'], actual['rows'], strict=True):
            assert new['pair'] == old['pair']
            for key, old_value in old.items():
                if key == 'pair':
                    continue
                old_number, new_number = Decimal(old_value), Decimal(new[key])
                difference = abs(old_number - new_number) / max(abs(old_number), Decimal('1e-50'))
                largest = max(largest, difference)
                assert difference < Decimal(protocol['relative_agreement_limit']), (new['pair'], key)
report = {'status': 'PASS', 'pair_count': 5, 'source_commit': os.environ['GITHUB_SHA'],
          'run_id': os.environ['GITHUB_RUN_ID'], 'run_attempt': os.environ.get('GITHUB_RUN_ATTEMPT', '1'),
          'run_url': os.environ['GITHUB_SERVER_URL'] + '/' + os.environ['GITHUB_REPOSITORY'] + '/actions/runs/' + os.environ['GITHUB_RUN_ID'],
          'saved_results_sha256': hashlib.sha256((source / 'gap-study-results.json').read_bytes()).hexdigest(),
          'replay_results_sha256': hashlib.sha256((work / 'gap-study-results.json').read_bytes()).hexdigest(),
          'protocol_sha256': fresh['protocol_sha256'], 'script_sha256': fresh['script_sha256'],
          'maximum_relative_difference_from_saved': str(largest), 'checks': fresh['checks'],
          'scope': 'Five numerical gap diagnostics. Approximate roots and quadrature, separate from Lean and not a proof of RH.'}
(work / 'replay-receipt.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
