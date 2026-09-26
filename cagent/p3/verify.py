#!/usr/bin/env python3
"""Build dependencies and kernel-check every published P3 theorem sequentially."""
import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parent
LEAN = ROOT / 'lean'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}


def main():
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    subprocess.run([lake, 'build', '+ProofPursuit.P3.Enumeration', '+ProofPursuit.P3.Staircase', '+ProofPursuit.P3.Classification', '+ProofPursuit.P3.Necklace', '+ProofPursuit.P3.RankedClassification'], cwd=LEAN, check=True)
    version = subprocess.check_output([lake, 'env', 'lean', '--version'], cwd=LEAN, text=True).strip()
    files = ['Basic.lean', 'Enumeration.lean', 'Staircase.lean', 'NegativeCheck.lean',
             'Convergence.lean', 'Boundary.lean', 'Eventual.lean', 'Energy.lean',
             'CyclicStep.lean', 'Diagonal.lean', 'DiagonalOrder.lean', 'HighestDiagonal.lean',
             'BoundaryReconstruction.lean', 'Classification.lean', 'Necklace.lean',
             'TriangularGeneral.lean', 'RankedClassification.lean'] + [f'N{n}.lean' for n in range(1, 24)]
    records = []
    started = time.monotonic()
    for name in files:
        path = 'ProofPursuit/P3/' + name
        command = [lake, 'env', 'lean', '-DwarningAsError=true', path]
        t = time.monotonic()
        result = subprocess.run(command, cwd=LEAN, capture_output=True, text=True, timeout=180)
        output = result.stdout + result.stderr
        audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", output)
        axiom_free = re.findall(r"'([^']+)' does not depend on any axioms", output)
        if result.returncode:
            raise RuntimeError(f'{path}:\n{output}')
        if name not in ['Basic.lean', 'Enumeration.lean'] and not (audits or axiom_free):
            raise RuntimeError(f'Missing axiom audit: {path}')
        for theorem, names in audits:
            unexpected = {a.strip() for a in names.split(',') if a.strip()} - ALLOWED
            if unexpected:
                raise RuntimeError(f'{theorem}: unexpected axioms {unexpected}')
        record = dict(file=path, command=['lake']+command[1:], seconds=round(time.monotonic()-t, 3),
                      exit_code=result.returncode, output=output)
        records.append(record)
        print(f'{name}: PASS ({record["seconds"]}s)', flush=True)
    checked_sources = [LEAN/'ProofPursuit/P3'/name for name in files]
    pinned_config = [LEAN/name for name in ['lean-toolchain', 'lakefile.toml', 'lake-manifest.json']]
    inputs = {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in sorted(checked_sources + pinned_config) if p.is_file()}
    inputs['verify.py'] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    report = dict(lean_version=version, source_sha256=inputs, records=records,
                  total_seconds=round(time.monotonic()-started, 3), status='PASS')
    (ROOT/'evidence/verification.json').write_text(json.dumps(report, indent=2)+'\n')
    print(f'All checks passed in {report["total_seconds"]} seconds.')


if __name__ == '__main__':
    main()
