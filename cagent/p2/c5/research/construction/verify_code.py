"""Verify the published (9,20,4) seed and its three-layer Q9 path count."""

from __future__ import annotations

CODE = [
    0, 63, 85, 90, 99, 142, 147, 184, 201, 228,
    263, 281, 298, 365, 368, 417, 438, 450, 476, 507,
]


def path_count(order: list[int]) -> int:
    assert sorted(order) == list(range(512))
    counts = [0] * 512
    for vertex in order:
        counts[vertex] = max(
            1, sum(counts[vertex ^ (1 << bit)] for bit in range(9))
        )
    return sum(counts)


def three_layer_order(code: list[int]) -> list[int]:
    root_set = set(code)
    return (
        sorted(code)
        + [vertex for vertex in range(512) if vertex.bit_count() % 2]
        + [
            vertex for vertex in range(512)
            if vertex.bit_count() % 2 == 0 and vertex not in root_set
        ]
    )


if __name__ == "__main__":
    assert len(set(CODE)) == 20
    assert all(vertex.bit_count() % 2 == 0 for vertex in CODE)
    assert min((a ^ b).bit_count() for i, a in enumerate(CODE) for b in CODE[i+1:]) == 4
    order = three_layer_order(CODE)
    assert path_count(order) == 2400
    print("code size 20, minimum distance 4, path count 2400")
