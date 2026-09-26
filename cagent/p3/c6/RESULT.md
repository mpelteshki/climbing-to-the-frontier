# P3 C6 — residue \(r=3\): the exact value of \(D_B(T_{k-1}+3)\)

Fable P3 C6 research output (Claude Fable 5.1 High). Isolated workspace; only `output/` written. Nothing published or submitted.

## 0. Result and status

Write \(T_j=j(j+1)/2\), \(n=T_{k-1}+3\), \(F=(k-1)(k-5)\).

**Theorem.** \(D_B(T_{k-1}+3)\) equals

| \(k\) | 3 | 4 | 5 | 6 | 7 | 8 | \(\ge 9\) |
|---|---|---|---|---|---|---|---|
| \(n\) | 6 | 9 | 13 | 18 | 24 | 31 | \(T_{k-1}+3\) |
| \(D_B(n)\) | 6 | 7 | 9 | 13 | 18 | 24 | \((k-1)(k-5)\) |

Status of each part:

* **\(k\ge 14\): complete written proof** (Section 5: lower bound Section 4, upper bound Section 5). It reuses the C1 cycle classification, the C2 lifetime/retreat lemmas and the C3 final-pattern dichotomy, each of which was re-derived by reading and independently stress-tested (Section 2). New ingredients: an exact entry-state lemma at every sandwich width, two inverse-tree height lemmas (single and double dominant pile), explicit orbit exclusions, and explicit inverse branches.
* **\(9\le k\le 14\): exhaustive computation** (\(n=39,48,58,69,81,94\); Section 3), each partition visited exactly once by backward layering, layer sizes summed against \(p(n)\). The written argument also covers \(k=14\), giving an overlap check. For \(9\le k\le 13\) the written argument closes every case except type I sandwiches of width \(k-5\) (and \(k-4\) at \(k=9\)) and, at \(k=9\), one width-\((k-4)\) type II state; those thirteen plus one explicit entry states are listed with their finite closure in Section 6 but the theorem for these \(k\) rests on the exhaustive enumeration.
* **\(3\le k\le 8\): exhaustive computation**; these are the pieces \(r=k\) (\(k=3\)), \(r=k-1\) (\(k=4\)) and the middle residues (\(k=5,\dots,8\)) of Griggs–Ho Theorem 4.5, and they match Griggs–Ho Figure 1.

**Beyond \(r=3\) (Section 9, added in the second session).** The same method, automated as a certificate checker, proves 24 further exact values \(D_B(T_{k-1}+r)=(k-1)(k-r-2)\) for \(r=4..7\) and \(70\le n\le 217\) (far beyond enumeration), and \(D_B(n)=L(n)\) is verified exhaustively for every \(n\le 70\). Two sharp inverse-height lemmas are identified (tested on all partitions of \(n\le 34\)) which, if proved, make the small-residue formula for each fixed \(r\le 8\) follow uniformly for \(2r+5\le k\le 40\) by a two-minute certificate, and would make the case analysis uniform in \(k\).

All values agree with Griggs–Ho Conjecture 4.7. The \(k\ge 9\) case is, to the extent of the literature check in Section 7, not proved in the literature; Griggs–Ho verified \(n\le 36\) (\(k\le 8\) for \(r=3\)), Grok's snapshot verified \(n\le 50\) (\(k\le 10\)). The exhaustive values for \(n=58,69,81,94\) are new finite evidence, and the written proof for \(k\ge 14\) is new work modulo the cited prerequisites.

Everything is replayable: `sh output/code/replay.sh` (78 s; add `full` for \(k=14\), about 5 more minutes). Evidence JSON files are in `output/evidence/`.

## 1. Definitions and conventions

A partition is a weakly decreasing tuple of positive integers. \(B\) removes one card from every pile, deletes empty piles, adds a pile equal to the previous number of piles, and sorts. \(\lambda\) is cyclic if \(B^i(\lambda)=\lambda\) for some \(i\ge 1\); \(d_B(\lambda)=\min\{i\ge 0: B^i(\lambda)\text{ cyclic}\}\); \(D_B(n)=\max_{\lambda\vdash n}d_B(\lambda)\).

Time index \(i\ge 1\) refers to the state \(B^{i-1}(\lambda)\); \(c_i\) is its number of piles. The pile created by move \(i\) (from time \(i\) to \(i+1\)) has size \(c_i\) and is present at times \(i+1,\dots,i+c_i\); its interval is \(J_i=[i+1,i+c_i]\). An original pile of size \(a\) is present at times \(1,\dots,a\). If \(d_i\) intervals end at time \(i\), then \(c_{i+1}=c_i+1-d_i\); so a rise by one means no death, a constant pair means exactly one death.

Ferrers diagrams: columns \(j\ge 0\), rows \(i\ge 1\); the cell \((i,j)\) lies on diagonal \(i+j\). Before sorting, a move sends \((i,j)\) with \(i>1\) to \((i-1,j+1)\) and \((1,j)\) to \((j+1,0)\); on diagonal \(w\) the column index advances by one modulo \(w\). Sorting is needed only if the unsorted column list is not weakly decreasing.

Inverse rule (Lemma I). For \(\mu\) with \(m\) parts, the predecessors of \(\mu\) are exactly the partitions \(R_s(\mu)\), one for each distinct part value \(s\ge m-1\) of \(\mu\): remove one part \(s\), add \(1\) to every other part, append \(s-m+1\) ones. Proof: the newborn pile of the move into \(\mu\) is one of its parts, \(s\), and the predecessor had \(s\) parts; the other \(m-1\) parts of \(\mu\) are the survivors minus one card; the \(s-(m-1)\) predecessor parts that vanished were ones. Call \(m-1\) the *threshold* of \(\mu\). The *inverse height* \(h(\mu)\) is the largest \(p\) such that some non-cyclic \(\lambda\) has \(B^p(\lambda)=\mu\); it is finite. If \(B^p(\lambda)=\mu\) then \(d_B(\lambda)\le p+d_B(\mu)\), and \(p\le h(\mu)\) whenever \(\lambda\) is non-cyclic.

## 2. Prerequisites: what is reused, how it was checked

Primary source: Griggs and Ho, *The cycling of partitions and compositions under repeated shifts*, Adv. Appl. Math. 21 (1998) 205–227, PDF `https://people.math.sc.edu/griggs/cycling.pdf` (read in full). Codex snapshot: `context/codex-p3/c5/submission.md` (SHA-256 `3a88188d…`), whose Appendices A–C restate C1–C3.

**(P1) Cycle classification** (Brandt; Griggs–Ho Theorem 2.1; C1 / Appendix A). For \(n=T_{k-1}+r\), \(1\le r\le k\), the cyclic partitions are exactly \((k-1+\varepsilon_0,\dots,\varepsilon_{k-1})\) with bits of weight \(r\), trailing zero omitted. Checked: I read the energy proof (diagonal energy non-increasing, strictly decreasing under a real sort; a hole on diagonal \(w\) under a cell on diagonal \(w+1\) is rotated into a forced sort because \(\gcd(w,w+1)=1\)); it is sound. Independently: `check_prereqs.py` compares this form against direct cycle detection for every partition of every \(n\le 40\) (215,307 partitions, PASS). Consequences used: a rank-\(k\) cyclic state has \(k-1\) or \(k\) parts, all parts \(\le k\), no cell above diagonal \(k\), adjacent differences in \(\{0,1,2\}\), and never three equal parts.

**(P2) Lifetime bookkeeping, card budget, retreat lemma, width-two lemma** (Griggs–Ho Prop. 3.2, Lemmas 3.5–3.6; C2 / Appendix B). For a sandwich \((c_p,\dots,c_q)=(x-1,x,\dots,x,x+1)\) of width \(L=q-p\ge 2\): \(p\le x(L-1)\), and \(p\le x\) if \(L=2\). Checked: read the C2 proof (largest absent recent interval \(u\); \(c_u=y-1,c_{u+1}=y\); induction along the plateau forces a shorter earlier sandwich of level \(\le x\) starting in \([p-x,p+1]\)); it is the Griggs–Ho argument written out and is sound. Numerically: every sandwich in every trajectory of every partition of \(n\le 40\) (973,004 sandwiches) satisfies \(p\le x(L-1)\); minimum slack is \(0\), so the bound is sharp. Also checked: \(c_{i+1}=c_i+1-d_i\) by explicit interval bookkeeping; the budget \(\sum_{j<m}c_{p+j}\le n+T_{m-1}\); and the special full-width bound \(p+k\le n+1\) (7,254 instances). The special bound is *not* needed below (Lemma D supersedes it).

**(P3) Final-pattern dichotomy** (Griggs–Ho Lemma 3.3(2)/4.3; C3 / Appendix C). For \(1\le r<k\), let \(t\) be the smallest index with \(c_t=k-1\), \(c_{t+1}=k\) and \(c_{t+i}=c_{t+k+i}\) for all \(i\ge 0\). Then \(B^{t-1}(\lambda)\) is cyclic, \(d_B(\lambda)\le t-1\), and if \(t\ge k+1\) either a **type I** sandwich \((k-1,k,\dots,k,k+1)\) with \(t-k\le p<q\le t-1\), or a **type II** sandwich \((k-2,k-1,\dots,k-1,k)\) with \(t-k+1\le p<q\le t+1\) occurs. Checked: read (the residual case forces condition (B), hence an earlier cyclic state, contradicting minimality); numerically verified for every partition of every \(n\le 40\) with \(1\le r<k\), including the index ranges.

**(P4) Inverse rule** (Lemma I): for every partition of every \(n\le 40\), `set(predecessors(mu))` equals the set of all \(\lambda\) with \(B(\lambda)=\mu\) found by scanning all partitions.

**Audit of the Codex C5 (\(r=2\)) proof.** Read in full. I re-derived: the excess distributions at widths \(k-3\), \(k-2\), \(k\); cyclicity of \((3,0,0),(2,1,0),A_k,B_k\); the \(S_k\) exclusion (cell on diagonal \(k+1\) for \(k-2\) moves); the \(P_k\), \(P'_k\), \(Q_1\), \(Q_2\) branches (they are instances of Lemmas D and D2 below plus the width-two lemma); the \(U_7,U_8\) finite closures; \(d=p\) at width \(k-2\). No gap found. `audit_c5_r2.py` independently confirms for \(k=7..30\): entry states, unique non-cyclic predecessors \(P_k=(k+1,k-1,k-3,\dots,2)\), \(P'_k=(k,k,k-3,\dots,2)\), \(S_k\) exclusion without sorting, \(h(A_k)\le n-k+1\), \(h(B_k)\le 3+\lfloor F/4\rfloor\) (\(k\le 12\)), \(U_7\) layers \(1,1,1,1,2,3,4,4\), \(U_8\) layers \(1,1\), forward depths \(5,6\), and \(D_B(T_{k-1}+2)=2,3,5,8,12,18,28,40,54\) for \(k=2..10\). Astra's checker was replayed read-only (`evidence/astra-check-replay.log`, PASS, 11 s). The Astra PASS was not used as authority for anything; every reused statement above was checked as described. Old Grok claims that \(r=2\) has no proof reflect a stale snapshot and are superseded.

## 3. Exact values by exhaustive enumeration (\(k=3..14\))

`exhaustive_r3.py` computes layers backward from the cyclic states: layer \(0\) = the \(\binom{k}{3}\) boundary states (each also confirmed cyclic by direct iteration), layer \(j+1\) = all predecessors of layer \(j\) (cyclic predecessors excluded at the first step). Every partition has exactly one successor, so it lies in exactly one layer and predecessors of distinct states are distinct; no hash set is needed. The run asserts \(\sum_j|\text{layer}_j|=p(n)\), so coverage is exhaustive by construction, and \(D_B(n)\) is the index of the last non-empty layer. Sampled states in each layer and every state of the last layer are re-checked by direct forward iteration.

| \(k\) | \(n\) | \(p(n)\) | \(D_B(n)\) | GH value | # maximizers | seconds |
|---|---|---|---|---|---|---|
| 3 | 6 | 11 | 6 | 6 | 1 | 0.0 |
| 4 | 9 | 30 | 7 | 7 | 1 | 0.0 |
| 5 | 13 | 101 | 9 | 9 | 1 | 0.0 |
| 6 | 18 | 385 | 13 | 13 | 1 | 0.0 |
| 7 | 24 | 1,575 | 18 | 18 | 31 | 0.0 |
| 8 | 31 | 6,842 | 24 | 24 | 1 | 0.01 |
| 9 | 39 | 31,185 | 32 | 32 | 1,466 | 0.05 |
| 10 | 48 | 147,273 | 45 | 45 | 4,551 | 0.22 |
| 11 | 58 | 715,220 | 60 | 60 | 28,742 | 1.5 |
| 12 | 69 | 3,554,345 | 77 | 77 | 136,072 | 8.8 |
| 13 | 81 | 18,004,327 | 96 | 96 | 617,403 | 49 |
| 14 | 94 | 92,669,720 | 117 | 117 | 2,823,652 | 288 |

Unique maximizers at \(k=5,6,8\): \((1^n)\). At \(k=7\) there are 31 maximizers of depth 18, including \((1^{24})\) and \((5,5,4,3,3,2,1,1)\). For \(k\ge 9\) the Griggs–Ho family (Section 4) is among the maximizers. Files: `evidence/exhaustive-r3-k{3..14}.json` (layer-size profiles included; the largest layers are the last ones, about 6% of \(p(n)\)).

These are theorems about the listed \(n\) only.

## 4. Lower bound: the Griggs–Ho family at \(r=3\) (reproduction, with the omitted calculation)

Griggs–Ho Theorem 4.5 case (1) requires \(1\le r<\lfloor (k-1)/2\rfloor\); for \(r=3\) this is \(k\ge 9\), and the stated value \((k-3-r)k+r+2=(k-1)(k-5)\). Their proof says "imitating the proof of Theorem 3.1"; here is the calculation.

**Theorem A.** For \(k\ge 9\), \(\lambda_k=(k-2,\,k-2,\,k-3,\dots,5,\,4,\,4,\,3,\,2,\,1)\) (\(k\) parts: \(\lambda_1=k-2\), \(\lambda_i=k-i\) for \(2\le i\le k-4\), \(\lambda_{k-3..k}=4,3,2,1\)) has \(d_B(\lambda_k)=(k-1)(k-5)\).

Relative to the staircase \((k-1,k-2,\dots,1,0)\), \(\lambda_k\) has one hole on diagonal \(k-1\) at column \(0\) and four extra cells on diagonal \(k\) at columns \(k-4,k-3,k-2,k-1\). For \(0\le s<F\) write \(s=a(k-1)+b\), \(0\le a\le k-6\), \(0\le b\le k-2\). Claim: \(B^s(\lambda_k)\) is the staircase with the hole at column \(b\) and extra cells at columns \((b-a-1-j)\bmod k\), \(j=0,1,2,3\). Each unreduced value \(b-a-1-j\) is either in \([0,b-1]\) or negative, in which case adding \(k\) gives \(b+(k-a-1-j)\ge b+2\) because \(k-a-1-j\ge k-(k-6)-1-3=2\); there is a single wrap since \(b-a-1-j\ge -(k-2)\). So no extra cell sits in the hole column or the column right of it. Heights relative to the staircase change by \(-1\) at the hole and \(+1\) at extra columns; an adjacent inversion needs \(-1\) immediately left of \(+1\), excluded; a vertical gap needs \(+1\) at the hole column, excluded. Hence every such diagram is a partition, the unsorted move equals the move, and diagonals \(k-1\) and \(k\) rotate by one column each move, proving the claim by induction. Each state with \(s<F\) has a hole on diagonal \(k-1\), so is not cyclic by (P1). At \(s=F\): \(a=k-5\), \(b=0\); the previous state's rotation puts the hole at column \(0\) and extras at \(1,2,3,4\); unsorted heights \((k-2,k-1,k-2,k-3,k-4,k-6,\dots,1)\); sorting swaps the first two, giving \((k-1,k-2,k-2,k-3,k-4,k-6,\dots,1)\), the boundary word with ones at positions \(2,3,4\): cyclic. So \(d_B(\lambda_k)=F\). \(\square\)

Checked by following the actual sorted move for \(k=9..300\) (`lower_family_r3.py`, PASS; direct classification-free depth for \(k\le 25\)). For \(k=6,7,8\) the same tuple has depth \(5,12,21<D_B\); for \(k=5\) the index ranges collapse. So the family is optimal exactly from \(k=9\), consistent with the middle-residue regime \(k\le 8\).

Name the terminal cyclic state \(S^*=(k-1,k-2,k-2,k-3,k-4,k-6,\dots,1)\).

## 5. Upper bound for \(k\ge 14\)

**Theorem B.** For \(k\ge 14\) and every \(\lambda\vdash n=T_{k-1}+3\), \(d_B(\lambda)\le F=(k-1)(k-5)=k^2-6k+5\).

Throughout, \(\lambda\) is fixed, \(c_i\) its counts, \(t\) as in (P3), \(d=d_B(\lambda)\le t-1\). If \(t\le k\) then \(d\le k-1<F\). Assume \(t\ge k+1\); by (P3) a type I or II sandwich occurs. Write \(S=B^p(\lambda)\), the state at time \(p+1\) (right after the first rise). The cyclic state \(B^{t-1}(\lambda)\) equals \(B^{t-1-p}(S)\) with \(0\le t-1-p\le k-1\) (type I) or \(\le k-2\) (type II). Useful numbers: \(n-k+1=(k^2-3k+8)/2\); \(F-(n-k+1)=(k^2-9k+2)/2\ge 1\) for \(k\ge 9\), so

\[
n-k+2\le F\quad(k\ge 9),\qquad n-3\le F\iff (k-1)(k-10)\ge 0\quad(k\ge 10).\tag{5.0}
\]

### 5.1 Entry-state lemma

**Lemma E.** Let \((c_p,\dots,c_q)=(x-1,x,\dots,x,x+1)\), width \(L=q-p\), and suppose \(2\le L\le x-1\). Then at time \(p+1\) the state \(S\) has \(x\) parts: the newborn \(J_p\) of size \(x-1\), and \(x-1\) old piles of which exactly one has each size \(1,2,\dots,L-2\), none has size \(L-1\), and the remaining \(x-L+1\) have size \(\ge L\). Width \(L=x\) is impossible.

Proof. \(c_{p+1}=x\) and \(J_p=[p+1,p+x-1]\) is present, so there are \(x-1\) old piles. For \(1\le j\le L-2\), \(c_{p+j}=c_{p+j+1}=x\), so exactly one interval ends at time \(p+j\); none ends at \(p+L-1\) because \(c_{p+L}=x+1\). Newborns \(J_{p+j}\) (\(j\ge 1\)) have size \(x\) and end at \(p+j+x\ge p+L\). \(J_p\) ends at \(p+x-1\); if \(L=x\) this is \(p+L-1\), where no interval ends: contradiction. If \(L\le x-1\), \(J_p\) ends at or after \(p+L\). So the intervals ending at \(p+1,\dots,p+L-2\) are old piles of sizes \(1,\dots,L-2\), one each; an old pile of size \(L-1\) would end at \(p+L-1\); every other old pile has size \(\ge L\). \(\square\)

Type II with \(x=k-1\): Lemma E covers \(L\le k-2\) and shows \(L=k-1\) is impossible. Full width \(L=k\) (type II): \(J_p\) ends at \(p+k-2\); deaths occur exactly at \(p+1,\dots,p+k-2\), one each, none at \(p+k-1\). \(J_p\) is the death at \(p+k-2\); the \(k-2\) old piles supply the deaths at \(p+1,\dots,p+k-3\) (sizes \(1,\dots,k-3\)) and one survivor of size \(\notin\{1,\dots,k-1\}\), i.e. \(\ge k\). Cards: \((k-2)+T_{k-3}+s=n\) gives \(s=k+2\). So

\[
S=W:=(k+2,\,k-2,\,k-3,\dots,1)\qquad(\text{type II, }L=k).\tag{5.1}
\]

For type II width \(L\le k-2\), the minimum card count is \((k-2)+T_{L-2}+(k-L)L\), and the *excess* \(E_L=n-\min\) is distributed among the \(k-L\) free old piles of base size \(L\): \(E_{k-2}=3\), \(E_{k-3}=4\), \(E_{k-4}=6\), and in general \(E_{k-1-r}=T_r\) at residue \(r\) (verified algebraically; see Section 6). For type I (\(x=k\), \(L\le k-1\)): minimum \((k-1)+T_{L-2}+(k-L+1)L\), which increases with \(L\) (successive difference \(k-L-1\)); at \(L=k-5\) it equals \(n+(k-13)\).

### 5.2 Generic widths and type I

**Type I, \(k\ge 14\).** The minimum at \(L=k-5\) exceeds \(n\), so \(L\le k-6\). By (P2), \(p\le k(L-1)\le k(k-7)\), and \(t-1\le p+k-1\) (since \(p\ge t-k\)). Hence \(d\le k(k-7)+k-1=k^2-6k-1=F-6\).

**Type II, \(L\le k-5\).** \(p\le (k-1)(L-1)\le(k-1)(k-6)\) and \(t-1\le p+k-2\) (since \(p\ge t-k+1\)): \(d\le (k-1)(k-6)+k-2=F-1\).

**Type II, \(L=k-1\):** impossible (Lemma E).

Remaining: type II with \(L\in\{k-4,k-3,k-2,k\}\). For these the retreat bound alone gives \(p\le F\), \(F+(k-1)\), \(F+2(k-1)\) and (special bound) \(n+1-k\) respectively, which is insufficient except when \(S\) is cyclic at \(L=k-4\). The rest of the proof determines \(S\) in each case and bounds either the inverse height of \(S\) or the length of the count pattern.

### 5.3 Two inverse-height lemmas

**Lemma D (single dominant pile).** Let \(\mu\vdash n\) have a unique largest part \(M\) exceeding every other part by at least \(3\) (or \(\mu=(n)\)). Then every inverse chain from \(\mu\) has length at most \(n-M+1\); in particular \(h(\mu)\le n-M+1\).

Proof. Consider an inverse chain \(\mu=\mu^0,\mu^1,\dots\) with \(B(\mu^{i+1})=\mu^i\). Call a step *tail-selecting* if the removed part is not the dominant one. Invariant along tail-selecting steps: the state has a unique dominant part exceeding the others by \(\ge 3\). Indeed, removing a tail part \(s\) (with \(s\ge m-1\)) adds one to the dominant part and to every other tail part (gap preserved) and appends ones, which are at most (new dominant) \(-3\) because the dominant part is at least \(4\) whenever a tail exists. Each tail-selecting step raises the dominant part by one at fixed total \(n\), and a tail-selecting step needs a non-empty tail; so at most \(n-M\) tail-selecting steps occur, the last possible one producing \((n)\). A *head* step removes the dominant part \(M'\) from a state with \(m\) parts: the result has \(M'\) parts, consisting of tail parts plus one (each \(\le M'-2\)) and ones, so its largest part is below its threshold \(M'-1\) and it has no predecessor. (From \((n)\) the head step gives \((1^n)\), which has no predecessor for \(n\ge 3\).) Hence a chain is at most \(n-M\) tail steps followed by at most one head step. \(\square\)

**Lemma D2 (two dominant piles).** Let \(\mu\vdash n\) have largest parts \(M\ge M'\ge 3\) (possibly equal) and every other part \(\le M'-3\). Then \(h(\mu)\le\lfloor (n-M-M')/2\rfloor+2\).

Proof. Tail-selecting steps (removing a part \(\le M'-3\)) raise both distinguished parts by one and preserve "every other part \(\le M'-3\)" (tail parts gain one; new ones are \(1\le M'-2\)). After \(i\) tail steps the distinguished parts hold \(M+M'+2i\le n\) cards, so \(i\le\lfloor (n-M-M')/2\rfloor\). Head steps: (a) remove \(M\) from a state with \(m\) parts: the result has \(M\) parts, threshold \(M-1\), parts \(M'+1\), tail\(+1\le M'-2\), and ones; only \(M'+1\) can be eligible (needs \(M'\ge M-2\)); removing it yields \(M'+1\) parts with all parts \(\le\max(M'-1,2)<M'\), below the threshold \(M'\): no predecessor. (b) remove \(M'<M\): the result has \(M'\) parts, threshold \(M'-1\), parts \(M+1\), tail\(+1\le M'-2\), ones; only \(M+1\) is eligible; removing it yields \(M+1\) parts, all \(\le\max(M'-1,2)<M\), below threshold \(M\). So at most two steps follow the tail steps. \(\square\)

Both lemmas were tested against exhaustive inverse trees of every partition of every \(n\le 32\) satisfying the hypotheses (23,025 and 11,732 cases; PASS; equality is attained, e.g. 339 and 907 tight cases), see `evidence/verify-claims-r3-k60-n32.log`.

**Lemma R (rotation exclusion).** If a partition \(S\) of \(n\) (rank \(k\)) has a cell on diagonal \(k+1\) and for \(0\le j\le k-3\) the unsorted move from \(B^j(S)\) yields a weakly decreasing column list, then \(B^j(S)\) has a cell on diagonal \(k+1\) for all \(0\le j\le k-2\) and none of these \(k-1\) states is cyclic. Proof: without sorting, a cell on diagonal \(k+1\) stays on diagonal \(k+1\); a rank-\(k\) cyclic state has no cell above diagonal \(k\) by (P1). \(\square\)

### 5.4 Type II, width \(L=k-4\) (retreat: \(p\le (k-1)(k-5)=F\))

By Lemma E, \(S\) consists of the newborn \(k-2\), old piles \(1,\dots,k-6\), and four old piles \(k-4+e_i\) with \(e_1\ge e_2\ge e_3\ge e_4\ge 0\), \(\sum e_i=6\). The nine excess vectors and the resulting \(S\) (\(\sigma\) denotes the tail \(k-6,k-5,\dots\) written as \(k-6,\dots,1\)):

| \(e\) | \(S\) | status |
|---|---|---|
| \((3,2,1,0)\) | \((k-1,k-2,k-2,k-3,k-4,\sigma)=S^*\) | cyclic |
| \((4,2,0,0)\) | \((k,k-2,k-2,k-4,k-4,\sigma)\) | cyclic |
| \((4,1,1,0)\) | \((k,k-2,k-3,k-3,k-4,\sigma)\) | cyclic |
| \((3,3,0,0)\) | \((k-1,k-1,k-2,k-4,k-4,\sigma)\) | cyclic |
| \((6,0,0,0)\) | \(S_6=(k+2,k-2,k-4,k-4,k-4,\sigma)\) | Lemma D |
| \((5,1,0,0)\) | \(S_{51}=(k+1,k-2,k-3,k-4,k-4,\sigma)\) | Lemma D, \(d_B=1\) |
| \((3,1,1,1)\) | \(S_{3111}=(k-1,k-2,k-3,k-3,k-3,\sigma)\) | width-two sandwich |
| \((2,2,2,0)\) | \((k-2,k-2,k-2,k-2,k-4,\sigma)\) | impossible (Lemma R) |
| \((2,2,1,1)\) | \((k-2,k-2,k-2,k-3,k-3,\sigma)\) | impossible (Lemma R) |

Cyclicity: a state with \(k-1\) parts is cyclic iff it is \((k-1+\varepsilon_0,\dots,1+\varepsilon_{k-2})\) with three ones among \(\varepsilon_0..\varepsilon_{k-2}\); matching the five top parts \(\{k-2,k-4+e_i\}\) against \(\{k-1+\varepsilon_0,\dots,k-5+\varepsilon_4\}\) forces \(\varepsilon_4=1\) and then exactly the four listed vectors (checked for each \(k=9..60\) by `verify_claims_r3.py`).

*Cyclic \(S\).* The state at time \(p\) has \(c_p=k-2\) parts, hence is not cyclic; so \(d=p\le (k-1)(k-5)=F\). This is the only case in the whole proof where the bound is attained; \(\lambda_k\) of Section 4 realizes it with \(S=S^*\).

*\(S_6\).* Unique largest part \(k+2\), others \(\le k-2\): Lemma D gives \(p\le h(S_6)\le n-k-1\). Then \(d\le t-1\le p+k-2\le n-3\le F\) by (5.0) (\(k\ge 10\)).

*\(S_{51}\).* \(B(S_{51})=(k,k-1,k-3,k-4,k-5,k-5,k-7,\dots,1)\), the boundary with ones at positions \(0,1,5\): cyclic, so \(d\le p+1\). Lemma D (gap \(3\)): \(p\le n-k\). So \(d\le n-k+1\le F\).

*\(S_{3111}\).* Direct computation of the orbit (each step: the trailing \(1\) dies, a pile \(k-1\) is born, the block of three slides down):
\(B^j(S_{3111})=(k-1,\dots,k-2-j,\;(k-3-j)^3,\;k-6-j,\dots,1)\) with \(k-1\) parts for \(0\le j\le k-6\);
\(B^{k-5}=(k-1,k-2,\dots,3,2,2,2)\), \(k\) parts (no death);
\(B^{k-4}=(k,k-2,k-3,\dots,2,1,1,1)\), \(k+1\) parts;
\(B^{k-3}=(k+1,k-1,k-3,\dots,1)\), \(k-1\) parts;
\(B^{k-2}=(k,k-1,k-2,k-4,\dots,1)\), cyclic.
The counts at times \(p+k-5,p+k-4,p+k-3\) are \((k-1,k,k+1)\): a width-two sandwich of level \(k\), so by (P2) \(p+k-5\le k\), i.e. \(p\le 5\). Hence \(d\le t-1\le p+k-2\le k+3<F\).

*\((2,2,2,0)\) and \((2,2,1,1)\).* Relative to the staircase, \((2,2,2,0)\) has a hole on diagonal \(k-1\) at column \(0\), cells on diagonal \(k\) at columns \(2,3,4\), and a cell on diagonal \(k+1\) at column \(3\); \((2,2,1,1)\) has the same hole and diagonal-\(k\) cells, with the diagonal-\((k+1)\) cell at column \(4\). Under the unsorted move the hole advances mod \(k-1\), the diagonal-\(k\) cells mod \(k\), the top cell mod \(k+1\). For \(0\le j\le k-5\) nothing wraps: heights are staircase \(-1\) at column \(j\), \(+1\) at \(j+2,j+3,j+4\), plus \(+1\) at \(j+3\) (resp. \(j+4\)); the column list is \((\dots,k-2-j,k-2-j,k-2-j,k-2-j,k-4-j,\dots)\) resp. \((\dots,k-2-j,k-2-j,k-2-j,k-3-j,k-3-j,\dots)\), weakly decreasing; the top cell sits on a diagonal-\(k\) cell, the hole column carries no extra cell. At \(j=k-4,k-3,k-2\) the states are, for \((2,2,2,0)\): \((k,k-2,\dots,4,2,2,2,2)\), \((k,k-1,k-3,\dots,3,1,1,1,1)\), \((k+1,k-1,k-2,k-4,\dots,2)\); for \((2,2,1,1)\): \((k,k-2,\dots,4,2,2,2,1,1)\), \((k+1,k-1,k-3,\dots,3,1,1,1)\), \((k,k,k-2,k-4,\dots,2)\). All are partitions obtained without sorting and all keep the diagonal-\((k+1)\) cell. By Lemma R, \(B^j(S)\) is not cyclic for \(0\le j\le k-2\), contradicting that \(B^{t-1-p}(S)\) with \(t-1-p\le k-2\) is cyclic. These cases do not occur.

### 5.5 Type II, width \(L=k-3\) (retreat: \(p\le (k-1)(k-4)=F+k-1\))

\(S\) = newborn \(k-2\), old \(1,\dots,k-5\), three old piles \(k-3+e_i\), \(\sum e_i=4\). Write \(\tau=k-5,\dots,1\).

| \(e\) | \(S\) | status |
|---|---|---|
| \((3,1,0)\) | \(S_3=(k,k-2,k-2,k-3,\tau)\) | cyclic |
| \((2,2,0)\) | \(S_2=(k-1,k-1,k-2,k-3,\tau)\) | cyclic |
| \((4,0,0)\) | \(S_{400}=(k+1,k-2,k-3,k-3,\tau)\) | Lemma D, \(d_B=1\) |
| \((2,1,1)\) | \((k-1,k-2,k-2,k-2,\tau)\) | impossible (Lemma R) |

*\(S_{400}\).* \(B(S_{400})=(k,k-1,k-3,k-4,k-4,k-6,\dots,1)\), ones at positions \(0,1,4\): cyclic. Lemma D (gap \(3\)): \(p\le n-k\); \(d\le p+1\le n-k+1\le F\).

*\((2,1,1)\).* Cells on diagonal \(k\) at columns \(2,3\) and on diagonal \(k+1\) at column \(3\), no hole. For \(j\le k-4\) nothing wraps and the list is \((\dots,k-2-j,k-2-j,k-2-j,k-5-j,\dots)\) — at \(j=k-4\): \((k-1,\dots,3,2,2,2)\); at \(j=k-3\): \((k,k-2,\dots,1,1,1)\); at \(j=k-2\): \((k+1,k-1,k-3,\dots,1)\). Lemma R excludes the case.

*\(S_3\) (cyclic, so \(d=p\)).* Threshold \(k-2\); eligible parts \(k\) and \(k-2\). \(R_k(S_3)=(k-1,k-1,k-2,k-4,\dots,2,1,1)\) is cyclic (ones at \(1,2,k-1\)), so if \(p\ge 1\) the state at time \(p\) is
\(P=R_{k-2}(S_3)=(k+1,k-1,k-2,k-4,k-5,\dots,2)\), \(k-2\) parts, threshold \(k-3\), eligible \(k+1,k-1,k-2\).
 – \(P_a=R_{k-2}(P)=(k+2,k,k-3,\dots,3,1)\): Lemma D2 with \(M=k+2,M'=k\), others \(\le k-3\): \(h(P_a)\le\lfloor (n-2k-2)/2\rfloor+2\).
 – \(P_b=R_{k-1}(P)=(k+2,k-1,k-3,\dots,3,1,1)\), \(k-1\) parts, threshold \(k-2\), eligible \(k+2,k-1\). \(R_{k-1}(P_b)=(k+3,k-2,\dots,4,2,2,1)\): Lemma D (gap \(5\)), \(h\le n-k-2\). \(R_{k+2}(P_b)=(k,k-2,\dots,4,2,2,1,1,1,1)\) has \(k+2\) parts and largest part \(k\) below its threshold \(k+1\): no predecessor. So \(h(P_b)\le n-k-1\).
 – \(Q=R_{k+1}(P)=(k,k-1,k-3,\dots,3,1,1,1,1)\), \(k+1\) parts, threshold \(k\): unique predecessor \(R=R_k(Q)=(k,k-2,\dots,4,2,2,2,2)\), \(k\) parts, threshold \(k-1\): unique predecessor \(R_3=R_k(R)=(k-1,\dots,5,3,3,3,3,1)\), \(k\) parts, threshold \(k-1\), whose only eligible value is \(k-1\), so every predecessor of \(R_3\) has \(k-1\) parts. If the chain from \(\lambda\) reaches beyond \(R_3\), the counts at the times of (predecessor of \(R_3\)), \(R_3\), \(R\), \(Q\) are \((k-1,k,k,k+1)\), a width-3 sandwich of level \(k\); by (P2) it starts at time \(\le 2k\), so \(Q\) is at time \(\le 2k+3\), \(P\) at \(\le 2k+4\), and \(p+1\le 2k+5\). Otherwise \(p\le 4\).
Altogether \(p\le\max\bigl(2+\lfloor (n-2k-2)/2\rfloor+2,\;1+1+(n-k-1),\;2k+4\bigr)=n-k+1\le F\) (using \(n\ge 3k+3\) for \(k\ge 7\)).

*\(S_2\) (cyclic, \(d=p\)).* Threshold \(k-2\); \(R_{k-1}(S_2)=(k,k-1,k-2,k-4,\dots,1)\) is cyclic, so the state at time \(p\) is \(P'=R_{k-2}(S_2)=(k,k,k-2,k-4,\dots,2)\), \(k-2\) parts, threshold \(k-3\), eligible \(k,k-2\).
 – \(R_{k-2}(P')=(k+1,k+1,k-3,\dots,3,1)\): Lemma D2 (\(M=M'=k+1\)), \(h\le\lfloor (n-2k-2)/2\rfloor+2\).
 – \(X_1=R_k(P')=(k+1,k-1,k-3,\dots,3,1,1,1)\), \(k\) parts, threshold \(k-1\). \(R_{k-1}(X_1)=(k+2,k-2,\dots,4,2,2,2)\): Lemma D (gap \(4\)), \(h\le n-k-1\). \(X_2=R_{k+1}(X_1)=(k,k-2,\dots,4,2,2,2,1,1)\), \(k+1\) parts, threshold \(k\): unique predecessor \(X_3=(k-1,k-2,\dots,5,3,3,3,2,2)\) with \(k\) parts, threshold \(k-1\), all of whose predecessors have \(k-1\) parts; the counts \((k-1,k,k+1)\) at (pred of \(X_3\)), \(X_3\), \(X_2\) form a width-two sandwich of level \(k\), so \(X_2\) is at time \(\le k+2\) and \(p+1\le k+5\).
Altogether \(p\le\max\bigl(2+\lfloor (n-2k-2)/2\rfloor+2,\;3+(n-k-1),\;k+4\bigr)=n-k+2\le F\) by (5.0).

### 5.6 Type II, width \(L=k-2\) (retreat: \(p\le (k-1)(k-3)=F+2(k-1)\))

\(S\) = newborn \(k-2\), old \(1,\dots,k-4\), two old piles \(k-2+e_i\), \(e_1+e_2=3\).

*\((3,0)\): \(S_{30}=(k+1,k-2,k-2,k-4,\dots,1)\).* \(B(S_{30})=(k,k-1,k-3,k-3,k-5,\dots,1)\), ones at \(0,1,3\): cyclic. Lemma D (gap \(3\)): \(d\le p+1\le n-k+1\le F\).

*\((2,1)\): \(S_{21}=(k,k-1,k-2,k-4,\dots,1)\), cyclic, \(d=p\).* Threshold \(k-2\), eligible \(k,k-1,k-2\). \(R_k(S_{21})=(k,k-1,k-3,\dots,2,1,1)\) is cyclic (ones at \(0,1,k-1\)). The two non-cyclic predecessors:
 – \(P_2=R_{k-2}(S_{21})=(k+1,k,k-3,\dots,2)\): Lemma D2 (\(M=k+1,M'=k\), others \(\le k-3\)): \(h\le\lfloor (n-2k-1)/2\rfloor+2\).
 – \(P_1=R_{k-1}(S_{21})=(k+1,k-1,k-3,\dots,2,1)\), \(k-1\) parts, threshold \(k-2\), eligible \(k+1,k-1\). \(R_{k-1}(P_1)=(k+2,k-2,k-3,\dots,1)=W\): Lemma D (gap \(4\)), \(h(W)\le n-k-1\). \(Q'=R_{k+1}(P_1)=(k,k-2,\dots,2,1,1,1)\), \(k+1\) parts, threshold \(k\): unique predecessor \(R_q=(k-1,k-2,\dots,3,2,2,2)\), \(k\) parts, threshold \(k-1\), all of whose predecessors have \(k-1\) parts; width-two sandwich \((k-1,k,k+1)\) at level \(k\) gives \(Q'\) at time \(\le k+2\), so \(p+1\le k+4\).
Altogether \(p\le\max\bigl(1+\lfloor (n-2k-1)/2\rfloor+2,\;2+(n-k-1),\;k+3\bigr)=n-k+1\le F\).

### 5.7 Type II, full width \(L=k\)

\(S=W=(k+2,k-2,\dots,1)\) by (5.1). \(B(W)=(k+1,k-1,k-3,\dots,1)\) is not cyclic; \(B^2(W)=(k,k-1,k-2,k-4,\dots,1)\) is cyclic. Lemma D: \(p\le n-k-1\). So \(d\le p+2\le n-k+1\le F\). (This replaces the special lifetime bound \(p+k\le n+1\), which at \(k=9\) would leave a deficit of one.)

### 5.8 Conclusion

Every case gives \(d\le F\): type I (\(k\ge 14\)); type II widths \(\le k-5\), \(k-4\) (Section 5.4, needs \(k\ge 10\) for \(S_6\)), \(k-3\), \(k-2\), \(k\); width \(k-1\) impossible. With Theorem A, \(D_B(T_{k-1}+3)=(k-1)(k-5)\) for all \(k\ge 14\), and together with Section 3 for all \(k\ge 9\). \(\blacksquare\)

Every explicit predecessor, orbit, cyclicity and count claim in Sections 5.4–5.7 is machine-checked for \(k=9..60\) in `verify_claims_r3.py` (`evidence/verify-claims-r3.json`, `verify-claims-r3-k60-n32.log`), and the exact inverse heights for \(k\le 13\) are recorded there (\(h(S_{21})=n-k+1\), \(h(W)=n-k-1\), \(h(S_3)=n-k-4\), \(h(S_2)=13,14,16,18,20\), \(h(S_{3111})=5\), \(h(S_6)=k-1\)).

## 6. Where the obstruction sits; what the finite data covers

**The sharp case.** The whole argument is tight in exactly one place: type II width \(k-4\) with the cyclic entry state \(S^*\), where the retreat bound \(p\le(k-1)(L-1)\) equals \(F\) *exactly* and the Griggs–Ho family attains it. In general, for residue \(r\), the retreat bound at width \(L=k-1-r\) is \((k-1)(k-2-r)=F_r\), the excess is \(E=T_r\) spread over \(r+1\) free piles of base \(k-1-r\) (algebra: \(n-\min=\tfrac12[(r+2)(2k-3-r)-2(r+1)(k-1-r)-2k+2r+4]=T_r\)). For \(r=2\): \(E=3\) over three piles (the C5 states \((3,0,0),(2,1,0),(1,1,1)\)), witness entry vector \((2,1,0)\); for \(r=3\): \(E=6\) over four piles (Section 5.4), witness entry vector \((3,2,1,0)\). Whether the witness's entry vector is \((r,\dots,1,0)\) for every \(r\) was not checked beyond \(r\le 3\). So the sharp case is closed for every \(r\) by the retreat lemma alone; the work is in the *other* excess vectors and the wider widths \(k-r,\dots,k-2,k\).

**What closes the other cases and why.** Every non-sharp entry state at \(r=3\) either (i) has a dominant pile and falls to Lemma D/D2 with \(h\lesssim n-k+2\approx k^2/2\ll F\); (ii) is excluded by Lemma R (a cell on diagonal \(k+1\) survives \(k-2\) unsorted moves); or (iii) forces a count pattern \((k-1,k,k+1)\) or \((k-1,k,k,k+1)\) a bounded number of steps back, so the width-two/retreat lemma gives \(p=O(k)\). The inverse heights of the cyclic entry states at widths \(k-3,k-2\) are governed by the \((1^n)\) chain: \(h(S_{21})=n-k+1\) is attained by \((1^n)\) itself (\(S_{21}\) is Griggs–Ho's terminal state \(U_{r-1}\) of the all-ones trajectory), and \(W=(k+2,k-2,\dots,1)\) is their \(\rho_{k-2}\). This is why the small-residue formula holds exactly while \(F_r\ge n-k+1\), i.e. up to \(r<\lfloor (k-1)/2\rfloor\); for larger \(r\) the all-ones chain through these entry states is longer, matching the middle-residue piece of Conjecture 4.7. This observation is heuristic beyond \(r\le 3\), not a proof.

**Finite-only parts for \(9\le k\le 13\).** The written argument fails only at type I: the card budget admits width \(k-5\) for \(k\le 13\) and width \(k-4\) for \(k=9\), and the retreat bound there gives \(d\le F+k-6\). The surviving entry states are thirteen explicit partitions (`evidence/typeI-entry-states-k9-13.json`): at \(k=9\), \((8,8,4^5,2,1)\) [\(h=2,\delta=6\)], \((8,7,5,4^4,2,1)\) [\(h=18,\delta=6\)], \((8,5^5,3,2,1)\) [\(h=1,\delta=7\)], and \((8,6,6,4^4,2,1)\), \((8,6,5,5,4^3,2,1)\), \((8,5^4,4,4,2,1)\) excluded (\(\delta\ge 15>k-1\)); at \(k=10\), \((9,8,5^5,3,2,1)\) [\(h=2,\delta=7\)] and two excluded (\(\delta=35\)); at \(k=11,12,13\) all excluded (\(\delta=49,65,83>k-1\)). Also at \(k=9\), \(S_6\) needs \(h(S_6)=8\) rather than Lemma D's \(29\). Each of these is a finite check at a fixed \(k\) (orbit of length \(\le k\), or a small inverse tree), so a written proof for \(9\le k\le 13\) could be completed by listing them; but the theorem for these \(k\) is already established by the exhaustive enumeration of Section 3, which is the cleaner certificate. Extending the type I exclusion (\(\delta\) grows like \(F\) for these six-equal-pile states) to a uniform argument was not attempted.

## 7. Literature and novelty check

* Griggs–Ho (1998), Theorem 4.5 case (1): the family and lower bound \((k-1)(k-5)\) for \(r=3\), \(k\ge 9\) — **reproduced** (Section 4, with the "imitate Theorem 3.1" calculation written out). Conjecture 4.7: equality — **open** in the paper; their data covers \(n\le 36\), i.e. only \(k\le 8\) for \(r=3\), where the value is a middle residue. Their Lemmas 3.3–3.6, 4.3, Theorem 4.4 are the pile-count machinery reused (P2, P3); Theorem 4.4 gives only \(k^2-2k-1\).
* Codex C5 (2026, snapshot): \(r=2\) for \(k\ge 7\) — audited (Section 2); its method (budget + retreat + inverse trees) is the template; the \(r=3\) case needed the additional Lemmas E, D, D2, R and the sandwich-in-the-inverse-chain arguments, and has more type II entry states at generic \(k\) (16 vs 6).
* Web search (26 Sep 2026) for resolutions of Conjecture 4.7 found none: Eriksson–Jonsson (Fibonacci Quart. 2017) and the survey arXiv:2607.17194 (2026) both cite it as open. The search was not exhaustive; no priority claim is made beyond "not found".
* New here: exhaustive values \(D_B(58)=60\), \(D_B(69)=77\), \(D_B(81)=96\), \(D_B(94)=117\) (beyond Grok's \(n\le 50\)); the complete written upper bound for \(r=3\), \(k\ge 14\); Lemmas D, D2, E, R as stated; the identification of the sharp case and the \(T_r\)-excess structure.

## 8. Replay

From `output/code/` (Python 3 standard library, single process, no network):

```sh
sh replay.sh          # 78 s on this machine: prerequisites n<=36, exhaustive k=3..13, family k<=120,
                      # symbolic claims k<=40 and lemma tests n<=26, entry-state table, C5 audit
sh replay.sh full     # + k=14 (n=94, 92,669,720 partitions, 288 s, about 2 GB)
python3 check_prereqs.py 40                 # 24 s, evidence/prereqs-check.json
python3 exhaustive_r3.py 12 14              # evidence/exhaustive-r3-k12..14.json
python3 lower_family_r3.py 9 300            # 229 s, evidence/lower-family-r3.json
python3 verify_claims_r3.py 9 60 32         # evidence/verify-claims-r3.json
python3 entry_states_r3.py 9 11             # evidence/entry-states-r3-k9..11.json (h, delta table)
python3 audit_c5_r2.py 30                   # evidence/audit-c5-r2.json
python3 exhaustive_general.py 51 52 ... 70  # evidence/exhaustive-general.log, exhaustive-n*.json (n=95: 107 s)
python3 toolkit_general_r.py 4 11 30        # certificate checker (r=4); 5 13 30, 6 15 30, 7 17 30, 8 19 30 (18 min total)
python3 toolkit_general_r.py 4 11 40 dprime # same with conjectural Lemma D'' as extra rule (fast)
python3 lower_family_general.py 4 11 40     # Griggs-Ho family depths, r=4 (also 5..8)
python3 lemma_conjectures_test.py 34        # Lemmas D'', O, O3 on all partitions n<=34
```

Recorded evidence: `evidence/exhaustive-r3-k{3..14}.json`, `exhaustive-r3-k12-14.log`, `prereqs-check.json`, `prereqs-check-n40.log`, `lower-family-r3.json`, `verify-claims-r3.json`, `verify-claims-r3-k60-n32.log`, `entry-states-r3-k{9,10,11}.json`, `typeI-entry-states-k9-13.json`, `audit-c5-r2.json`, `astra-check-replay.log`. Context snapshot hashes: `context/manifest.json` (source HEAD e45c2b715b170c04ca777b6d3c0c7c3814d4e253). Machine: macOS, 24 GB, load ~7 from other tasks; all runs single-threaded.

## 9. General small residues: certificates, and what a uniform proof needs

### 9.1 Exhaustive values for all \(n\le 70\)

`exhaustive_general.py` (same backward layering, \(p(n)\) coverage assertion) gives \(D_B(n)=L(n)\) for every \(n\le 70\) — previously \(n\le 36\) (Griggs–Ho) and \(n\le 50\) (Grok) — and additionally for \(n=81,82,94,95\). Log: `evidence/exhaustive-general.log`, files `evidence/exhaustive-n*.json`. Largest run: \(n=95\), 104,651,419 partitions, 107 s. All residues in \(k=10,11\) are included; e.g. \(D_B(61)=51\) (\(k=11,r=6\), the middle residue, unique maximizer \((1^{61})\)), \(D_B(66)=110\).

### 9.2 The certificate checker (`toolkit_general_r.py R KMIN KMAX`)

For \(n=T_{k-1}+r\), \(r<\lfloor (k-1)/2\rfloor\), \(F=(k-1)(k-r-2)\), the script re-runs the Section 5 argument mechanically: it enumerates every sandwich (type I level \(k\), type II level \(k-1\)) and width not closed by the generic bound, derives the entry states by Lemma E (excess \(E_L\) over the free piles; \(E_{k-1-r}=T_r\)), and closes each entry state \(S\) by the first applicable rule:

1. `cyclic-retreat`: \(S\) cyclic and \(x(L-1)\le F\);
2. `rotation-excluded`: Lemma R (\(\delta(S)>\) allowed moves and a diagonal-\((k+1)\) cell survives without sorting);
3. `lemmaD` / `lemmaD2`: Lemma D or D2 bound on \(h(S)\), plus \(\delta(S)\) if \(\delta\le\) allowed moves, else the generic \(k-1\) / \(k-2\);
4. `forward-sandwich`: the orbit of \(S\) shows a level-\(k\) sandwich, so retreat bounds the time of \(S\);
5. `branch`: DFS over all inverse chains of non-cyclic states from \(S\), each branch closed by a dead end, a sandwich in the chain's own count sequence (retreat lemma), Lemma D or Lemma D2; the maximum over leaves bounds \(p\).

Every rule is one of the proven implications of Section 5 (each rule's justification is the corresponding paragraph there), so a run with no `UNCLASSIFIED` entry is a proof of \(D_B(n)\le F\) for that \(n\); with the Griggs–Ho family (`lower_family_general.py`, direct iteration) it is a proof of equality. Calibration: on \(r=3\) the checker reproduces Section 5 exactly, closing \(k\ge 10\) (and \(k=9\) up to \(S_6\)).

**Theorem C (certificate-based, exact values).** \(D_B(T_{k-1}+r)=(k-1)(k-r-2)\) for
\(r=4\), \(k=12..21\) (\(n=70,82,95,109,124,140,157,175,194,214\); \(D_B=66,84,104,126,150,176,204,234,266,300\));
\(r=5\), \(k=15..21\) (\(n=110,125,141,158,176,195,215\); \(D_B=112,135,160,187,216,247,280\));
\(r=6\), \(k=17..20\) (\(n=142,159,177,196\); \(D_B=144,170,198,228\));
\(r=7\), \(k=19..21\) (\(n=178,197,217\); \(D_B=180,209,240\)).
Evidence: `evidence/toolkit-r{4..8}-k*-30.json` (per-state tags; the \(r=6,7,8\) files are gzipped because of their size), `evidence/lower-family-r{4..8}.json`. The three values with \(n\le 95\) agree with the independent exhaustive enumeration. These are computer-assisted proofs for the listed \(n\) (each is a finite, inspectable case tree, typically \(10^3\)–\(10^5\) nodes), not statements about all \(k\).

Failures at other \(k\) are of two kinds and both are artefacts of the checker, not mathematical obstructions: (i) for \(k\le 2r+4\) the type I width window survives the card budget, exactly as at \(r=3\), \(k\le13\); (ii) for \(k\ge 22\) the DFS exceeds its node limit because the inverse trees of the cyclic entry states at widths \(k-r,\dots,k-2\) grow with \(k\) before reaching Lemma D/D2 leaves (the returned bounds, when it finishes, are always \(n-k+1\) or \(n-k+2\), the \((1^n)\)-chain heights). Tag counts are constant in \(k\) from \(k=2r+5\) on, so the case structure is uniform; what is missing for a theorem "for all \(k\)" is a uniform bound on those inverse heights.

### 9.3 Two sharp inverse-height lemmas (conjectural), and what they buy

Exhaustive inverse trees of every non-cyclic partition of every \(n\le 34\) (`lemma_conjectures_test.py`, `evidence/lemma-conjectures-test.json`) support:

**Lemma D″ (tall part).** If \(\mu\) has \(m\) parts and \(\mu_1\ge m+3\), then \(h(\mu)\le n-\mu_1+1\). Tight at \(\mu=(n)\). This is Lemma D's bound with the gap condition \(\mu_1-\mu_2\ge 3\) replaced by \(\mu_1-m\ge 3\). Sharp: at \(\mu_1=m+2\) it fails by up to \(20\) (\((8,6,5,4,3,2)\), \(n=28\), \(h=41\)).

**Lemma O (four ones).** If \(\mu\) has at least four parts equal to \(1\), then \(h(\mu)\le n-m\). Tight at \((1^n)\). Sharp: with exactly three ones it fails by up to \(20\) (\((7,6,5,4,3,1,1,1)\), \(n=28\), \(h=40\)).

Reduction (proved): D″ follows from O together with the intermediate case O3 (\(\mu_1=m+2\) with \(\ge3\) ones \(\Rightarrow h\le n-\mu_1+1\), also verified \(n\le 34\)). Track the tall part as an anchor along an inverse chain from \(\mu\): a step removing a part \(s\le\mu_1-2\) keeps the anchor tall and raises it by one (bound drops by one); a step removing a copy of \(\mu_1\) (either the anchor or a duplicate) leaves a state with \(\mu_1\) parts and \(\mu_1-m+1\ge 4\) ones, to which O gives \(h\le n-\mu_1\); a step removing a part \(\mu_1-1\) leaves \(\mu_1-1\) parts, largest \(\mu_1+1=m'+2\) and \(\ge 3\) ones, which is O3. Induction on chain length closes. I did not find proofs of O or O3. Data for the natural induction (track four equal piles of size \(a\), which grow by one per inverse step until one is removed): for all non-cyclic partitions of \(n\le 32\), four parts equal to \(a\ge 2\) give \(h\le n-m-a\) (tight at \((4,2,2,2,2)\), \((6,5,3,3,3,3,1)\)), and \(a=1\) gives \(h\le n-m\). The inductive step \(\nu\leftarrow R_s(\nu)\) with \(s\ge m\) preserves this bound with one unit to spare, but \(s=m-1\) (no ones appended, count drops by one) loses exactly one unit for \(a\ge 2\); the data show the bound survives, so the states reached by \(s=m-1\) steps (all parts \(\ge 2\), four equal parts \(a+1\ge 3\)) must satisfy the stronger \(h\le n-m-a-2\) — also true in the data for \(a+1\ge 3\) — but a potential that certifies this uniformly (equivalently, controls runs of forward moves with at most one death) was not found. Forward card counting alone cannot work: \(c_t\le n-t+1\) is false on deep transients, so any proof must use that the tall pile was born from a state with many small piles.

Consequence if D″ holds (checked with `toolkit_general_r.py R KMIN 40 dprime`, which adds D″ as a sixth rule; 2 minutes total): the checker closes \(r=4\) for \(k=13..40\), \(r=5\) for \(15..40\), \(r=6\) for \(17..40\), \(r=7\) for \(19..40\), \(r=8\) for \(22..40\) — i.e. every \(k\ge 2r+5\) tested (evidence: `evidence/toolkit-r*-dprime.json`). The remaining small-\(k\) windows are the type I widths, finite for each \(r\). Since the D″ leaves are reached after a bounded number of steps (independent of \(k\)) from each entry state, D″ is also precisely the statement that would make the whole case analysis uniform in \(k\), turning "small-residue Griggs–Ho for fixed \(r\)" into bookkeeping. This is the sharpest formulation of the upper-bound obstruction found here.

### 9.4 Lemma Dq and the unconditional closure of \(r=4\) for \(12\le k\le 40\)

**Lemma Dq (proved).** Let \(\mu\vdash n\) have parts \(M_1\ge\dots\ge M_q\ge 3\) such that every other part is \(\le M_q-3\). Then \(h(\mu)\le\lfloor (n-\sum_i M_i)/q\rfloor+q\). (Lemmas D and D2 are \(q=1,2\).)

Proof. Call the \(q\) parts distinguished. A tail step (removing a part \(\le M_q-3\)) adds one to every distinguished part and to every tail part and appends ones; the hypothesis is preserved (tail \(\le M_q-2=(M_q+1)-3\), ones \(\le M_q-2\) since \(M_q\ge 3\)), and the distinguished sum grows by \(q\) at fixed total \(n\), so at most \(\lfloor (n-\sum M_i)/q\rfloor\) tail steps occur. A head step removes a distinguished part \(D\) (current size) and yields threshold \(D-1\). Induction on the number \(t\) of head steps performed so far (with no tail step in between, as we now show): after \(t\) head steps every remaining distinguished part has grown by \(t\), tail parts are \(\le M_q-3+t\), one-derived parts are \(\le t\), and the threshold is (size of the last removed part)\(-1\ge M_q+t-2\); hence tail and one-derived parts are below the threshold and only distinguished parts are eligible. Each head step removes one distinguished part and none is ever created, so at most \(q\) head steps follow the tail steps, after which no part is eligible. \(\square\)

Numerically confirmed on all non-cyclic partitions of \(n\le 30\) for every admissible \(q\) (21,299 cases, 3,554 tight). Adding Lemma Dq as a DFS leaf rule to the certificate checker collapses the inverse trees: **\(r=3\) closes for all \(k=10..16\), and \(r=4\) closes for every \(k=12..40\) (\(n\) from 70 to 784), in 0.2 s total, with no conjectural input.** Hence, unconditionally,

\[
D_B(T_{k-1}+4)=(k-1)(k-6)\qquad\text{for all }12\le k\le 40 .
\]

(Lower bounds: `lower_family_general.py`, direct iteration.) The sweep of \(r=5..10\) with Lemma Dq was interrupted before completion; run `python3 toolkit_general_r.py R $((2R+3)) 40` to reproduce. Since the trees are now tiny and their tags are constant in \(k\), a written uniform proof for \(r=4\), all \(k\ge 12\), reduces to transcribing the \(k\)-parametrised case tree from the checker's output — the natural next step.

## 10. Caveats

* The written proof is mathematics in Markdown, not Lean. Prerequisites (P1)–(P3) are reused from Griggs–Ho / Codex with independent reading and finite stress tests, not re-formalized.
* For \(9\le k\le 13\) the theorem rests on exhaustive enumeration (Section 3), replayable in about a minute; the written argument is complete there except for the type I widths listed in Section 6 and \(S_6\) at \(k=9\).
* Section 6's remarks about general \(r\) beyond the \(T_r\)-excess identity are heuristics, not results.
* Number-of-maximizer counts are reported as computed and not analysed.
* Theorem C (Section 9.2) rests on the certificate checker's rules being exactly the proven implications of Section 5; the rules are listed there and the per-state tags are recorded, but the checker itself has not been audited by anyone else. Lemmas D″, O, O3 are conjectures with exhaustive evidence to \(n\le 34\), not results; everything derived from them is labelled conditional.
