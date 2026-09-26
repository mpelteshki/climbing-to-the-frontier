"""Random tests of local vertex-removal/projection inequalities.

Remove a vertex v; project its neighbors u_1..u_k onto v^perp and normalize.
Claim(k): sum_i delta(v,u_i) + sum_{i<j} delta(u_i,u_j) >= sum_{i<j} delta(u_i',u_j').
"""
import numpy as np
rng = np.random.default_rng(1)
def delta(a,b): return np.arcsin(min(1.0, abs(float(a@b))))
def test(k, d, trials, ortho=False, bessel_only=False):
    worst = np.inf; worst_cfg=None
    for _ in range(trials):
        v = rng.standard_normal(d); v/=np.linalg.norm(v)
        if ortho:
            # neighbors pairwise orthogonal unit vectors, random
            Q,_ = np.linalg.qr(rng.standard_normal((d,k)))
            U = Q.T
        else:
            U = rng.standard_normal((k,d)); U/=np.linalg.norm(U,axis=1,keepdims=True)
        lhs = sum(delta(v,u) for u in U) + sum(delta(U[i],U[j]) for i in range(k) for j in range(i+1,k))
        P = U - np.outer(U@v, v); n = np.linalg.norm(P,axis=1)
        if np.any(n<1e-9): continue
        P/=n[:,None]
        rhs = sum(delta(P[i],P[j]) for i in range(k) for j in range(i+1,k))
        if lhs-rhs < worst: worst=lhs-rhs; worst_cfg=(v,U)
    return worst, worst_cfg
for k in (1,2,3):
    for d in (3,4,6):
        w,_ = test(k,d,200000 if k<=2 else 100000)
        print(f"k={k} d={d} general: min(lhs-rhs)={w:.6f}")
for k in (3,4):
    for d in (4,6):
        w,_ = test(k,d,200000, ortho=True)
        print(f"k={k} d={d} neighbors pairwise orthogonal: min(lhs-rhs)={w:.6f}")
