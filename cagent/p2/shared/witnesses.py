"""Generate explicit labels; independently count paths by dynamic programming."""
import json
import argparse
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('--check', action='store_true', help='verify generated files without writing')
args = parser.parse_args()
base = Path(__file__).resolve().parent

def output_path(d, name):
    if base.name == 'shared':
        part = 'c1' if d <= 4 else f'c{d-3}' if d <= 6 else 'c4'
        return base.parent / part / name
    return base / name

def emit(path, content):
    if args.check:
        assert path.read_text() == content, f'generated file differs: {path}'
    else:
        path.write_text(content)

def code(gens):
    c=[0]
    for g in gens: c += [x^g for x in c]
    return sorted(c)

def count(d, order):
    assert sorted(order)==list(range(2**d))
    counts=[0]*(2**d)
    for v in order:
        counts[v]=max(1,sum(counts[v^(1<<k)] for k in range(d)))
    return sum(counts)

generators={3:[],4:[15],5:[15],6:[15,51],7:[15,51,85],8:[15,51,85,255]}
header='import Fast\n\nset_option maxRecDepth 1000000\nset_option maxHeartbeats 0\nnamespace Hypercube\n'
for d,gs in generators.items():
    roots=code(gs)
    order=roots+[v for v in range(2**d) if v.bit_count()%2]+[v for v in range(2**d) if v.bit_count()%2==0 and v not in roots]
    n=count(d,order)
    emit(output_path(d, f'q{d}.json'), json.dumps(order)+'\n')
    emit(output_path(d, f'q{d}-labels.txt'), '\n'.join(format(v,f'0{d}b') for v in order)+'\n')
    s=header+f'def q{d} : List Nat := {order}\n'
    s+=f'theorem q{d}_labelling : IsLabelling {d} q{d} := by unfold IsLabelling; decide\n'
    s+=f'theorem q{d}_count : pathCount {d} q{d} = {n} := by\n'
    s+=f'  rw [fast_count {d} q{d} q{d}_labelling]\n  decide\n'
    s+=f'theorem q{d}_witness : ∃ order, IsLabelling {d} order ∧ pathCount {d} order = {n} :=\n'
    s+=f'  ⟨q{d}, q{d}_labelling, q{d}_count⟩\n'
    s+=f'#print axioms q{d}_labelling\n#print axioms q{d}_count\n#print axioms q{d}_witness\nend Hypercube\n'
    emit(output_path(d, f'Q{d}.lean'), s)
    print(d, n, roots)
