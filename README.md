# Mantel's Theorem in Lean 4

Formalization of Mantel's Theorem in Lean 4 using `Mathlib`.

Theorem Overview

Mantel's Theorem (1907) is a fundamental result in extremal graph theory. It states that:
Any triangle-free graph $G$ with $n$ vertices has at most $\lfloor n^2 / 4 \rfloor$ edges.
---

##  Proof Strategy

The proof implemented in `Mantel.lean` follows a classic 3-step combinatorial approach:

1. Neighborhood Disjointness:
   - If $G$ is triangle-free, then adjacent vertices $u, v$ have disjoint neighbor sets $N(u) \cap N(v) = \emptyset$.
   - Consequently, $\deg(u) + \deg(v) \le n$ for every edge $\{u, v\} \in E$.

2. Double-Counting & Degree Sums:
   - By double-counting pairs $(v, w)$ across all edges, we establish:
     $$\sum_{v \in V} \sum_{w \in N(v)} (\deg v + \deg w) = 2 \sum_{v \in V} \deg(v)^2 \le 2 \cdot n \cdot |E|$$
   - Thus, $\sum_{v \in V} \deg(v)^2 \le n |E|$.

3. Cauchy-Schwarz & Handshaking Lemma:
   - Using Cauchy-Schwarz: $(\sum \deg v)^2 \le n \cdot \sum \deg(v)^2$.
   - By Handshaking Lemma: $\sum \deg v = 2|E|$.
   - Combining both yields $4|E|^2 \le n^2 |E|$, which simplifies to $4|E| \le n^2$.

---
## Dependencies & Setup

This project uses **Lean 4** and relies on **Mathlib 4**.

### Prerequisites
Make sure you have `elan` (the Lean version manager) installed. If not, install it via:
```bash
curl [https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh](https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh) -sSf | sh
### Build Instructions

Clone the repository:
   ```bash
   git clone [https://github.com/yndongmath/Mantel-s-theorem.git](https://github.com/yndongmath/Mantel-s-theorem.git)
   cd Mantel-s-theorem
---
