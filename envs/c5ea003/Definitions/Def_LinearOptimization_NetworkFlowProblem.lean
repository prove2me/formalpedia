-- Prove2me | Definitions.Def_LinearOptimization_NetworkFlowProblem
-- name    : LinearOptimization_NetworkFlowProblem
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T21:59:07.064121+00:00
-- url     : https://prove2.me/theorems/524d0dc3-c6b2-4843-9331-03319254a085
-- title:
--   Network flow problem and node-arc incidence matrix
-- statement:
--   **(The network flow problem, Bertsimas & Tsitsiklis, §7.1-7.2, pp. 267-278)**
--
--   A *network* is a directed graph $G=(\mathcal{N},\mathcal{A})$ — arcs are ordered pairs $(i,j)$ of distinct nodes (self-arcs are not allowed, p. 268) — together with external supplies $b_i$ for each node $i\in\mathcal{N}$, nonnegative (possibly infinite) capacities $u_{ij}$, and cost coefficients $c_{ij}$ per unit of flow along arc $(i,j)$.
--
--   A vector with components $f_{ij}$, $(i,j)\in\mathcal{A}$, is called a *flow*; it is a *feasible flow* if it satisfies flow conservation
--
--   $$b_i + \sum_{j\in I(i)} f_{ji} = \sum_{j\in O(i)} f_{ij}$$
--
--   for all $i\in\mathcal{N}$ (Eq. (7.1)) and the capacity constraints
--
--   $$0\le f_{ij}\le u_{ij}$$
--
--   for all $(i,j)\in\mathcal{A}$ (Eq. (7.2)). The minimum cost network flow problem minimizes
--
--   $$\sum_{(i,j)\in\mathcal{A}} c_{ij}f_{ij}$$
--
--   over all feasible flows; the problem is *uncapacitated* if $u_{ij}=\infty$ for all $(i,j)\in\mathcal{A}$ (then only the equality and nonnegativity constraints remain and the problem is in standard form, p. 273).
--
--   With $\mathcal{N}=\{1,\dots,n\}$, $m$ arcs, and a fixed ordering of the arcs, the *node-arc incidence matrix* $\mathbf{A}$ is the $n\times m$ matrix whose $(i,k)$th entry is $a_{ik}=1$ if $i$ is the start node of the $k$th arc, $-1$ if $i$ is the end node of the $k$th arc, and $0$ otherwise (p. 277); flow conservation reads $\mathbf{A}\mathbf{f}=\mathbf{b}$. Summing Eq. (7.1) over $i$ gives $\sum_{i\in\mathcal{N}} b_i=0$ — the book assumes this condition from p. 272 on (Assumption 7.1(a), p. 279). The *truncated node-arc incidence matrix* $\tilde{\mathbf{A}}$ is the $(n-1)\times m$ matrix consisting of the first $n-1$ rows of $\mathbf{A}$, and $\tilde{\mathbf{b}}=(b_1,\dots,b_{n-1})$ (p. 280).
--
--   A *circulation* is any flow vector with $\mathbf{A}\mathbf{f}=0$; the *simple circulation* $\mathbf{h}^C$ associated with a cycle $C$ with forward-arc set $F$ and backward-arc set $B$ has components $h^C_{ij}=1$ if $(i,j)\in F$, $-1$ if $(i,j)\in B$, $0$ otherwise, and the cost of the cycle is
--
--   $$\mathbf{c}'\mathbf{h}^C=\sum_{(i,j)\in F}c_{ij}-\sum_{(i,j)\in B}c_{ij}$$
--
--   (p. 278).
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, §7.1-7.2, pp. 267-278 (Eqs. (7.1)-(7.2) p. 272; incidence matrix p. 277; circulations p. 278; Assumption 7.1 p. 279; truncated matrix p. 280)

import Mathlib.Data.Matrix.Mul
import Mathlib.Data.ENNReal.Basic
import Mathlib.Logic.Relation

/-!
The minimum cost network flow problem: directed graphs, incidence
matrices, flows, circulations, walks/paths/cycles.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, §7.1–§7.2 (pp. 267–278) and §7.3 (pp. 279–280):

- **Graphs (§7.1, p. 268).** A directed graph `G = (𝒩, 𝒜)`: arcs are
  ordered pairs `(i, j)` of *distinct* nodes (self-arcs are not allowed;
  both `(i, j)` and `(j, i)` may be present). Walks, paths, and cycles
  traverse arcs irrespective of their direction, splitting the traversed
  arcs into *forward* and *backward* arcs (pp. 268–269); a path visits no
  node more than once; a cycle is a closed path. The graph is *connected*
  if for every pair of nodes there is a walk between them in the
  underlying undirected sense.
- **Notation flip (p. 279).** In Chapter 7, `n` = number of nodes and
  `m` = number of arcs — "the exact opposite" of the earlier chapters'
  convention. We keep Chapter 7's convention.
- **The problem (§7.2, pp. 272–273).** Data: external supplies `bᵢ`,
  capacities `uᵢⱼ ∈ [0, ∞]`, costs `cᵢⱼ`. A vector `f` of arc flows is a
  *feasible flow* if it satisfies flow conservation (Eq. (7.1)) and the
  capacity constraints `0 ≤ fᵢⱼ ≤ uᵢⱼ` (Eq. (7.2)); the problem minimizes
  `∑ cᵢⱼ fᵢⱼ`. It is *uncapacitated* if `uᵢⱼ = ∞` for all arcs — then only
  `Af = b`, `f ≥ 0` remain and the problem is in standard form (p. 273).
- **Incidence matrix (p. 277).** With a fixed ordering of the arcs, the
  node-arc incidence matrix `A` is the `n × m` matrix with `a_{ik} = 1` if
  `i` is the start node of the `k`th arc, `−1` if `i` is its end node, and
  `0` otherwise; flow conservation reads `Af = b`. Every column has
  exactly one `+1` and one `−1`, so the rows of `A` sum to zero — summing
  Eq. (7.1) forces the standing assumption `∑ᵢ bᵢ = 0` (p. 272,
  Assumption 7.1(a) p. 279).
- **Circulations (p. 278).** A *circulation* is a flow vector with
  `Af = 0`. The *simple circulation* `h^C` of a cycle `C` with forward-arc
  set `F` and backward-arc set `B` has components `+1` on `F`, `−1` on
  `B`, `0` elsewhere; the cost of the cycle is
  `c'h^C = ∑_F cᵢⱼ − ∑_B cᵢⱼ`.
- **Truncation (p. 280).** The truncated incidence matrix `Ã` is the
  `(n−1) × m` matrix of the *first* `n − 1` rows of `A` (the deleted last
  row — conservation at node `n` — is redundant), and `b̃ = (b₁, …, b_{n−1})`.

Design (see CLAUDE.md and the mission design note): the digraph is an
indexed arc family `arcs : Fin m → Fin n × Fin n` — the indexed family IS
the book's fixed arc ordering (parallel arcs allowed by the family;
injectivity is added as a hypothesis where the arc-set semantics matter).
The no-self-loop condition is the explicit predicate `HasNoSelfLoops`.
Walks are lists of steps `(k, dir) : Fin m × Bool` (`true` = the arc is
traversed forward, `false` = backward). Truncation is encoded over
`n + 1` nodes via `Fin.castSucc` (rows `0, …, n−1` of an `(n+1) × m`
matrix), avoiding `ℕ`-subtraction junk. Capacities live in `ℝ≥0∞`;
flows stay real, compared to capacities via `ENNReal.ofReal`.
Mission X (max-flow min-cut) imports this file.
-/

open Matrix
open scoped ENNReal

namespace LinearOptimization

/-- **Bertsimas & Tsitsiklis, §7.1 (p. 268).** The arc family has no self-arcs: every arc joins
two distinct nodes. (Part of the book's definition of a directed graph.) -/
def HasNoSelfLoops {n m : ℕ} (arcs : Fin m → Fin n × Fin n) : Prop :=
  ∀ k, (arcs k).1 ≠ (arcs k).2

/-- **Bertsimas & Tsitsiklis, §7.2 (p. 277).** The node-arc incidence matrix of the arc family
`arcs`: the `(i, k)` entry is `+1` if node `i` is the start node of arc
`k`, `−1` if it is its end node, and `0` otherwise. -/
def incidenceMatrix {n m : ℕ} (arcs : Fin m → Fin n × Fin n) :
    Matrix (Fin n) (Fin m) ℝ :=
  Matrix.of fun i k =>
    (if (arcs k).1 = i then (1 : ℝ) else 0) - (if (arcs k).2 = i then 1 else 0)

/-- **Bertsimas & Tsitsiklis, §7.2 (Eqs. (7.1)–(7.2), p. 272).** `f` is a feasible flow for
supplies `bsupply` and capacities `u`: flow conservation `Af = b` and the
capacity constraints `0 ≤ f_k ≤ u_k` for every arc `k`. -/
def IsFeasibleFlow {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (bsupply : Fin n → ℝ) (u : Fin m → ℝ≥0∞) (f : Fin m → ℝ) : Prop :=
  (incidenceMatrix arcs).mulVec f = bsupply ∧
  ∀ k, 0 ≤ f k ∧ ENNReal.ofReal (f k) ≤ u k

/-- **Bertsimas & Tsitsiklis, §7.2 (p. 278).** A circulation: a flow vector with `Af = 0`. -/
def IsCirculation {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (f : Fin m → ℝ) : Prop :=
  (incidenceMatrix arcs).mulVec f = 0

/-! ### Walks, paths, and cycles (Bertsimas & Tsitsiklis, §7.1, pp. 268–269)

A *step* is a pair `(k, dir)`: arc `k` traversed forward (`dir = true`,
from its start node to its end node) or backward (`dir = false`). -/

/-- The node at which the step `st` begins. -/
def stepStart {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (st : Fin m × Bool) : Fin n :=
  if st.2 then (arcs st.1).1 else (arcs st.1).2

/-- The node at which the step `st` ends. -/
def stepEnd {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (st : Fin m × Bool) : Fin n :=
  if st.2 then (arcs st.1).2 else (arcs st.1).1

/-- **Bertsimas & Tsitsiklis, §7.1 (pp. 268–269).** The list of steps `steps` is a walk from
`s` to `t`: consecutive steps match up, arcs traversed irrespective of
their direction. -/
def IsWalkFrom {n m : ℕ} (arcs : Fin m → Fin n × Fin n) :
    Fin n → Fin n → List (Fin m × Bool) → Prop
  | s, t, [] => s = t
  | s, t, st :: rest => stepStart arcs st = s ∧ IsWalkFrom arcs (stepEnd arcs st) t rest

/-- The nodes visited by a walk starting at `s`: `s` followed by the end
node of each step. -/
def walkNodes {n m : ℕ} (arcs : Fin m → Fin n × Fin n) (s : Fin n)
    (steps : List (Fin m × Bool)) : List (Fin n) :=
  s :: steps.map (stepEnd arcs)

/-- **Bertsimas & Tsitsiklis, §7.1 (p. 268).** A path from `s` to `t`: a walk that visits no
node more than once. -/
def IsPathFrom {n m : ℕ} (arcs : Fin m → Fin n × Fin n) (s t : Fin n)
    (steps : List (Fin m × Bool)) : Prop :=
  IsWalkFrom arcs s t steps ∧ (walkNodes arcs s steps).Nodup

/-- **Bertsimas & Tsitsiklis, §7.1 (p. 269).** A cycle at `s`: a nonempty closed walk whose
nodes are all distinct except that it ends where it starts, and which
traverses no arc twice. -/
def IsCycle {n m : ℕ} (arcs : Fin m → Fin n × Fin n) (s : Fin n)
    (steps : List (Fin m × Bool)) : Prop :=
  steps ≠ [] ∧ IsWalkFrom arcs s s steps ∧
  ((walkNodes arcs s steps).dropLast).Nodup ∧ (steps.map Prod.fst).Nodup

/-- **Bertsimas & Tsitsiklis, §7.2 (p. 278).** The signed arc-indicator vector of a list of
steps: `+1` on arcs traversed forward, `−1` on arcs traversed backward,
`0` elsewhere. For a cycle `C` this is the book's *simple circulation*
`h^C` (forward-arc set `F`, backward-arc set `B`); the cost of the cycle
is `c' ⬝ᵥ traversalVector steps = ∑_F c_k − ∑_B c_k`. The same vector for
a path `P` is the augmentation direction `h^P` of §7.5. -/
def traversalVector {m : ℕ} (steps : List (Fin m × Bool)) : Fin m → ℝ :=
  fun k => (if (k, true) ∈ steps then (1 : ℝ) else 0) -
    (if (k, false) ∈ steps then 1 else 0)

/-- Nodes `i` and `j` are joined by some arc, in either direction (the
underlying undirected adjacency, Bertsimas & Tsitsiklis, §7.1 p. 268). -/
def networkAdjacent {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (i j : Fin n) : Prop :=
  ∃ k, arcs k = (i, j) ∨ arcs k = (j, i)

/-- **Bertsimas & Tsitsiklis, §7.1 (p. 268).** The graph is connected: every node is reachable
from every other by a walk in the underlying undirected graph
(reflexive-transitive closure of the undirected adjacency). -/
def IsConnectedNetwork {n m : ℕ} (arcs : Fin m → Fin n × Fin n) : Prop :=
  ∀ i j : Fin n, Relation.ReflTransGen (networkAdjacent arcs) i j

/-! ### Truncation (Bertsimas & Tsitsiklis, §7.3, p. 280) -/

/-- **Bertsimas & Tsitsiklis, §7.3 (p. 280).** The truncated node-arc incidence matrix `Ã` of a
graph on `n + 1` nodes: the first `n` rows of `A` — the deleted last row is
the (redundant) flow conservation equation at the last node. -/
def truncatedIncidence {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1)) : Matrix (Fin n) (Fin m) ℝ :=
  (incidenceMatrix arcs).submatrix Fin.castSucc id

/-- **Bertsimas & Tsitsiklis, §7.3 (p. 280).** The truncated supply vector
`b̃ = (b₁, …, b_{n−1})`: the supplies at all nodes but the last. -/
def truncatedSupply {n : ℕ} (bsupply : Fin (n + 1) → ℝ) : Fin n → ℝ :=
  fun i => bsupply i.castSucc

end LinearOptimization


