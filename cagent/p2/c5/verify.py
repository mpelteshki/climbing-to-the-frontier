#!/usr/bin/env python3
"""Replay every embedded Python certificate from the published P2 C5 argument."""
from pathlib import Path
import hashlib
import json
import re
import subprocess
import sys
import time

source = Path(__file__).with_name('submission.md')
data = source.read_bytes()
blocks = re.findall(r'```python\n(.*?)\n```', data.decode(), flags=re.S)
assert len(blocks) == 4, f'Expected four certificate blocks, got {len(blocks)}'
results = []
for index, code in enumerate(blocks, 1):
    start = time.perf_counter()
    run = subprocess.run([sys.executable, '-c', code], capture_output=True, text=True)
    elapsed = time.perf_counter() - start
    if run.returncode:
        raise RuntimeError(f'Certificate {index} failed:\n{run.stdout}\n{run.stderr}')
    row = {'block': index, 'exit_code': run.returncode,
           'seconds': round(elapsed, 6), 'code_sha256': hashlib.sha256(code.encode()).hexdigest()}
    if index == 4:
        payload = json.loads(run.stdout)
        counts = payload['counts']
        assert counts['degree_multisets'] == 1110562
        assert counts['before_triple'] == 134
        assert counts['after_triple'] == 20
        assert counts.get('after_strengthened_cost', 0) == 0
        row['counts'] = counts
    results.append(row)
print(json.dumps({'source_sha256': hashlib.sha256(data).hexdigest(),
                  'python': sys.version, 'certificates': results}, indent=2))
