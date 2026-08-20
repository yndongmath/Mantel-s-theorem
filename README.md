# Mantel's Theorem in Lean 4

A complete formalization of **Mantel's Theorem** in Lean 4, built on top of [Mathlib](https://github.com/leanprover-community/mathlib4).

## Theorem

Mantel's Theorem (1907) is a foundational result in extremal graph theory:

> Any triangle-free graph $G$ on $n$ vertices has at most $\lfloor n^2 / 4 \rfloor$ edges.

The statement proved in [`Mantel.lean`](Mantel.lean) is the equivalent integer form (avoiding floors):

```lean
theorem mantel (hG : G.CliqueFree 3) :
    4 * G.edgeFinset.card ≤ (Fintype.card V) ^ 2
```

The proof is complete and axiom-clean — it depends only on the three standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) and contains no `sorry`.

## Proof strategy

The formalization follows the classic three-step combinatorial argument.

**1. Degree bound on each edge.**
If $G$ is triangle-free, adjacent vertices $u, v$ have disjoint neighborhoods, $N(u) \cap N(v) = \emptyset$. Since both neighborhoods sit inside $V$, this gives

$$\deg(u) + \deg(v) \le n \quad \text{for every edge } \{u, v\} \in E.$$

**2. Double counting the degree squares.**
Summing the previous bound over all ordered adjacent pairs $(v, w)$ and using $\sum_v \sum_{w \in N(v)} \deg(v) = \sum_v \sum_{w \in N(v)} \deg(w) = \sum_v \deg(v)^2$:

$$2 \sum_{v \in V} \deg(v)^2 = \sum_{v \in V} \sum_{w \in N(v)} \bigl(\deg(v) + \deg(w)\bigr) \le n \cdot 2|E|,$$

hence $\displaystyle \sum_{v \in V} \deg(v)^2 \le n\,|E|$.

**3. Cauchy–Schwarz and the handshake lemma.**
Cauchy–Schwarz gives $\bigl(\sum_v \deg(v)\bigr)^2 \le n \sum_v \deg(v)^2$, and the handshake lemma gives $\sum_v \deg(v) = 2|E|$. Combining,

$$4|E|^2 = \Bigl(\sum_v \deg(v)\Bigr)^2 \le n \sum_v \deg(v)^2 \le n \cdot n\,|E| = n^2 |E|,$$

and dividing by $|E| > 0$ yields $4|E| \le n^2$.

## Key lemmas

| Lemma | Statement |
|-------|-----------|
| `sum_sum_deg_self` | $\sum_v \sum_{w \in N(v)} \deg(v) = \sum_v \deg(v)^2$ |
| `sum_sum_deg_swap` | $\sum_v \sum_{w \in N(v)} \deg(w) = \sum_v \deg(v)^2$ |
| `deg_add_deg_le` | For an edge $u \sim v$ in a triangle-free graph, $\deg(u) + \deg(v) \le n$ |
| `sum_deg_sq_le` | $\sum_v \deg(v)^2 \le n\,|E|$ |
| `four_edges_sq_le` | $4|E|^2 \le n^2 |E|$ (Cauchy–Schwarz over $\mathbb{R}$, cast back to $\mathbb{N}$) |
| `mantel` | $4|E| \le n^2$ |

## Setup

This project uses **Lean 4** and **Mathlib 4**. The exact Lean version is pinned in the `lean-toolchain` file, so `elan` will fetch the right toolchain automatically.

### 1. Install `elan`

`elan` is the Lean version manager. If you don't have it yet:

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

(See the [Lean community setup guide](https://leanprover-community.github.io/get_started.html) for platform-specific instructions and the recommended VS Code extension.)

### 2. Clone and build

```bash
git clone https://github.com/yndongmath/Mantel-s-theorem.git
cd Mantel-s-theorem

# Download the prebuilt Mathlib cache FIRST.
# Without this, `lake build` recompiles all of Mathlib from source (hours).
lake exe cache get

# Build the project.
lake build
```

### 3. Explore interactively (optional)

Open the folder in VS Code with the **Lean 4** extension installed, then open `Mantel.lean`. The Lean InfoView on the right shows the proof state at the cursor.

## Verifying the proof

To confirm the proof is complete and free of `sorry`, add (or check) this line at the bottom of `Mantel.lean`:

```lean
#print axioms mantel
```

The expected output is:

```
'mantel' depends on axioms: [propext, Classical.choice, Quot.sound]
```

If `sorryAx` appears in that list, some part of the proof is still incomplete.

## Authors & credits

Developed during the **Utrecht University Summer School: *Formalizing Mathematics in Lean*** (2026).

- Yanni (Kelly) Dong
- Anastasiia (Stacey) Sharfenberg
