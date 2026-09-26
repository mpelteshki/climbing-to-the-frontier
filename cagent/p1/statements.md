# P1 — Angles between lines
Read in signed-in Chrome on 2026-09-26. Source: https://hackathon.bainsa.ai/p/p1

Lines through origin, repetitions allowed. For unit representatives x,y, θ(x,y)=arccos |⟨x,y⟩| ∈ [0,π/2]. S=Σ_{i<j} θ(x_i,x_j).

- C1 https://hackathon.bainsa.ai/p/p1/c1: For N lines in R², S≤(π/2)⌊N²/4⌋.
- C2 https://hackathon.bainsa.ai/p/p1/c2: For m≥2 unit vectors x₁,…,x_m in R^(m−1), with ⟨x_i,x_j⟩=0 whenever |i−j|≥2, prove Σ_{i=1}^{m−1} θ(x_i,x_{i+1})≤(m−2)π/2.
- C3 https://hackathon.bainsa.ai/p/p1/c3: For d≥1 and d+1 lines in R^d, S≤(choose(d+1,2)−1)π/2.
- C4 https://hackathon.bainsa.ai/p/p1/c4: Five lines in R³ satisfy S≤4π; six lines in R⁴ satisfy S≤13π/2.
- C5 https://hackathon.bainsa.ai/p/p1/c5: For d≥2 and d+2 lines in R^d, S≤(choose(d+2,2)−2)π/2.
- C6 https://hackathon.bainsa.ai/p/p1/c6: For N=qd+s, 0≤s<d, let M(N,d)=s choose(q+1,2)+(d−s) choose(q,2). Prove or disprove S≤(choose(N,2)−M(N,d))π/2. Open question. Infinite families beyond prior cells count as partial progress.

Full proofs required; citing target result insufficient. Computational proofs require rigorous exact/interval computation under ten minutes on laptop. No submission authorized.
