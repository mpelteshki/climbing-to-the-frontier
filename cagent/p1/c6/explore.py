"""Numerical exploration for P1 C6 (Fejes Toth angle-sum conjecture).

For N lines in R^d, deficiency D = sum_{i<j} arcsin|<x_i,x_j>|.
Conjecture (C6): D >= M(N,d)*pi/2, with M(N,d) = s*C(q+1,2) + (d-s)*C(q,2), N = q d + s.

This script runs random-restart local maximization of the angle sum S = C(N,2)pi/2 - D
(equivalently minimization of D) and reports the best value found, the gap to the
conjectured optimum, and the structure (nonorthogonality graph) of the best configurations.
Numerical evidence only; not a proof.
"""
import sys, math, itertools, json
import numpy as np
from scipy.optimize import minimize

def M(N, d):
    q, s = divmod(N, d)
    return s * (q + 1) * q // 2 + (d - s) * q * (q - 1) // 2

def deficiency(X):
    G = X @ X.T
    iu = np.triu_indices(len(X), 1)
    c = np.clip(np.abs(G[iu]), 0, 1)
    return float(np.sum(np.arcsin(c)))

def smooth_obj(flat, N, d, eps):
    # smoothed |t| ~ sqrt(t^2+eps^2) inside arcsin, to allow gradient descent through t=0
    X = flat.reshape(N, d)
    nrm = np.linalg.norm(X, axis=1, keepdims=True)
    U = X / nrm
    G = U @ U.T
    iu = np.triu_indices(N, 1)
    t = G[iu]
    r = np.sqrt(t * t + eps * eps)
    r = np.minimum(r, 1 - 1e-12)
    val = np.sum(np.arcsin(r))
    # gradient wrt t
    dr = (1 / np.sqrt(1 - r * r)) * (t / r)
    dG = np.zeros((N, N)); dG[iu] = dr; dG = dG + dG.T
    dU = dG @ U
    # chain through normalization
    dX = (dU - np.sum(dU * U, axis=1, keepdims=True) * U) / nrm
    return val, dX.ravel()

def optimize(N, d, restarts, rng, eps_sched=(0.1, 0.02, 0.005, 1e-3, 1e-4, 0.0)):
    best = None
    for _ in range(restarts):
        X = rng.standard_normal((N, d))
        for eps in eps_sched:
            if eps == 0.0:
                f = lambda z: smooth_obj(z, N, d, 1e-9)
            else:
                f = lambda z, e=eps: smooth_obj(z, N, d, e)
            res = minimize(f, X.ravel(), jac=True, method='L-BFGS-B',
                           options={'maxiter': 2000, 'ftol': 1e-14, 'gtol': 1e-10})
            X = res.x.reshape(N, d)
            X = X / np.linalg.norm(X, axis=1, keepdims=True)
        D = deficiency(X)
        if best is None or D < best[0] - 1e-12:
            best = (D, X)
    return best

def graph_info(X, tol=1e-6):
    G = X @ X.T
    N = len(X)
    A = (np.abs(G) > tol) & ~np.eye(N, dtype=bool)
    deg = A.sum(axis=1)
    rank = np.linalg.matrix_rank(G, tol=1e-7)
    return A, deg, rank

if __name__ == '__main__':
    cases = [(int(a), int(b)) for a, b in (arg.split(',') for arg in sys.argv[1:])] or \
        [(5,3),(6,3),(7,3),(6,4),(7,4),(8,4),(7,5),(8,5),(9,5),(8,6),(9,6),(10,6)]
    rng = np.random.default_rng(12345)
    out = []
    for N, d in cases:
        D, X = optimize(N, d, restarts=40, rng=rng)
        target = M(N, d) * math.pi / 2
        A, deg, rank = graph_info(X)
        G = X @ X.T
        iu = np.triu_indices(N, 1)
        c = np.clip(np.abs(G[iu]), 0, 1)
        near = int(np.sum(c > 1 - 1e-6))
        # Treat near-coincident pairs (|<x,y>| > 1 - 1e-6) as exactly coincident.  arcsin has a
        # square-root singularity at 1, so a pair with |<x,y>| = 1 - eps at double precision
        # loses about sqrt(2 eps) ~ 1.5e-8 of deficiency; this column removes that artifact.
        D_snap = float(np.sum(np.arcsin(np.where(c > 1 - 1e-6, 1.0, c))))
        rec = dict(N=N, d=d, M=M(N, d), best_D=D, target=target, gap=D - target,
                   near_coincident_pairs=near, D_snapped=D_snap, gap_snapped=D_snap - target,
                   rank=int(rank), degrees=sorted(int(x) for x in deg),
                   X=[[round(float(v), 12) for v in row] for row in X])
        print(json.dumps(rec))
        out.append(rec)
    json.dump(out, open('explore-results.json', 'w'), indent=1)
