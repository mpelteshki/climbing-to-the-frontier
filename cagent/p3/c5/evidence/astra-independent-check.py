"""Independent P3C5 audit replay; standard Python only.

Cycle detection uses actual repeated states, independently of C1. Additional
checks compare the written modular diagrams with actual sorted moves.
"""


def step(p):
    return tuple(sorted((len(p),) + tuple(x - 1 for x in p if x > 1), reverse=True))


def boundary(p, k):
    p = p + (0,) * (k - len(p))
    return len(p) == k and all(p[j] - (k - 1 - j) in (0, 1) for j in range(k))


def predecessors(p):
    m = len(p)
    for s in set(p):
        if s >= m - 1:
            q = list(p)
            q.remove(s)
            q = tuple(sorted([x + 1 for x in q] + [1] * (s - m + 1), reverse=True))
            assert step(q) == p
            yield q


def partitions(n, limit=None):
    if n == 0:
        yield ()
        return
    for a in range(min(n, limit or n), 0, -1):
        for q in partitions(n - a, a):
            yield (a,) + q


def depth(p, cache):
    path, seen, q = [], {}, p
    while q not in cache and q not in seen:
        seen[q] = len(path)
        path.append(q)
        q = step(q)
    if q in seen:
        for a in path[seen[q]:]:
            cache[a] = 0
        path = path[:seen[q]]
    for a in reversed(path):
        cache[a] = cache[step(a)] + 1
    return cache[p]


for k in range(2, 11):
    n, cache, count, maximum = k * (k - 1) // 2 + 2, {}, 0, 0
    for p in partitions(n):
        count += 1
        maximum = max(maximum, depth(p, cache))
    expected = [2, 3, 5, 8, 12][k - 2] if k < 7 else (k - 1) * (k - 4)
    assert maximum == expected
    assert all((d == 0) == boundary(p, k) for p, d in cache.items())
    print("exhaustive", k, n, count, maximum, flush=True)

for k in range(5, 151):
    p = (k - 2,) + tuple(k - i for i in range(2, k - 2)) + (3, 2, 1)
    final = (k - 1) * (k - 4)
    assert len(p) == k and sum(p) == k * (k - 1) // 2 + 2
    for t in range(final):
        a, b = divmod(t, k - 1)
        h = [k - 1 - j for j in range(k)]
        h[b] -= 1
        for j in ((b - a - 3) % k, (b - a - 2) % k, (b - a - 1) % k):
            h[j] += 1
        assert tuple(x for x in h if x) == p and not boundary(p, k), (k, t, p, h)
        p = step(p)
    assert boundary(p, k)
print("modular witness trajectory verified k=5..150", flush=True)

for k in range(7, 151):
    p = (k - 2,) * 4 + tuple(range(k - 5, 0, -1))
    for j in range(k - 1):
        h = [max(k - 1 - i, 0) for i in range(k + 1)]
        h[j] -= 1
        for c in ((j + 2) % k, (j + 3) % k):
            h[c] += 1
        h[(j + 3) % (k + 1)] += 1
        assert tuple(x for x in h if x) == p and not boundary(p, k), (k, j, p, h)
        p = step(p)
print("S_k exclusion trajectory verified k=7..150", flush=True)

for k, p in [(7, (6, 4, 3, 3, 3, 3, 1)), (8, (7, 4, 4, 4, 4, 4, 2, 1))]:
    layer, sizes = {p}, []
    while layer:
        sizes.append(len(layer))
        layer = {q for a in layer for q in predecessors(a)}
    sizes.append(0)
    expected = [1, 1, 1, 1, 2, 3, 4, 4, 0] if k == 7 else [1, 1, 0]
    assert sizes == expected
    assert depth(p, {}) == (5 if k == 7 else 6)
    print("U inverse layers", k, sizes, "depth", depth(p, {}), flush=True)
