-- Prove2me | Definitions.Def_LinearOptimization_TreeSolution
-- name    : LinearOptimization_TreeSolution
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-08-05T21:59:17.532367+00:00
-- url     : https://prove2.me/theorems/77707d3f-9fef-499b-bce9-106db2402dd6
-- title:
--   Tree solution of a network flow problem
-- statement:
--   **(Bertsimas & Tsitsiklis, Definition 7.1, p. 280)** A flow vector $\mathbf{f}$ is called a *tree solution* if it can be constructed by the following procedure:
--
--   - **(a)** pick a set $T\subset\mathcal{A}$ of $n-1$ arcs that form a tree when their direction is ignored;
--   - **(b)** let $f_{ij}=0$ for every $(i,j)\notin T$;
--   - **(c)** use the flow conservation equation $\tilde{\mathbf{A}}\mathbf{f}=\tilde{\mathbf{b}}$ to determine the flow variables $f_{ij}$, for $(i,j)\in T$.
--
--   A tree solution that also satisfies $\mathbf{f}\ge 0$ is called a *feasible tree solution*.
--
--   (Stated in §7.3 under standing Assumption 7.1, p. 279: $\sum_{i\in\mathcal{N}} b_i=0$ and the graph $G$ is connected; the problem is uncapacitated.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Definition 7.1, p. 280

import Definitions.Def_LinearOptimization_NetworkFlowProblem

/-!
Tree solutions of the uncapacitated network flow problem.

Source: Bertsimas & Tsitsiklis, *Introduction to Linear Optimization*,
Athena Scientific 1997, **Definition 7.1 (p. 280)**: "A flow vector `f` is
called a *tree solution* if it can be constructed by the following
procedure: (a) pick a set `T ⊂ 𝒜` of `n − 1` arcs that form a tree when
their direction is ignored; (b) let `fᵢⱼ = 0` for every `(i, j) ∉ T`;
(c) use the flow conservation equation `Ãf = b̃` to determine the flow
variables `fᵢⱼ` for `(i, j) ∈ T`. A tree solution that also satisfies
`f ≥ 0` is called a *feasible tree solution*." Stated in §7.3 under
standing Assumption 7.1 (p. 279): `∑ᵢ bᵢ = 0`, the graph is connected, and
the problem is uncapacitated.

Design (mission design note): encoded as a predicate — `IsTreeSolution f`
holds iff there is a set `T` of arc indices forming a spanning tree when
direction is ignored with `f = 0` off `T` and `Ãf = b̃`. Step (c)'s
"determine" (unique solvability of the tree system) is exactly
Theorem 7.3 (`network_tree_solution_unique`), so the predicate form avoids
a choice function. "Tree on the node set" = connected spanning subgraph
with `#nodes − 1` arcs (Bertsimas & Tsitsiklis, Theorem 7.2, p. 271, background); with `n + 1`
nodes the cardinality condition reads `T.card + 1 = n + 1`, avoiding
`ℕ`-subtraction. (Connected + `n − 1` distinct arcs already forces the
arcs of `T` to be non-parallel, non-self-loop, and acyclic.)
-/

open Matrix

namespace LinearOptimization

/-- Nodes `i` and `j` are joined, in either direction, by some arc whose
index lies in `T` (undirected adjacency of the subgraph spanned by `T`). -/
def networkAdjacentOn {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (T : Finset (Fin m)) (i j : Fin n) : Prop :=
  ∃ k ∈ T, arcs k = (i, j) ∨ arcs k = (j, i)

/-- **Bertsimas & Tsitsiklis, Definition 7.1(a) / Theorem 7.2 (pp. 271, 280).** The arc-index
set `T` forms a tree on the node set when arc directions are ignored:
`T` has `#nodes − 1` arcs (`T.card + 1 = n`) and the subgraph of the arcs
in `T` connects all nodes. -/
def IsTreeArcSet {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (T : Finset (Fin m)) : Prop :=
  T.card + 1 = n ∧
  ∀ i j : Fin n, Relation.ReflTransGen (networkAdjacentOn arcs T) i j

/-- **Bertsimas & Tsitsiklis, Definition 7.1 (p. 280).** `f` is a tree solution: for some set
`T` of arcs forming a tree when their direction is ignored, `f` vanishes
off `T` and satisfies the truncated flow conservation equation `Ãf = b̃`.
(On a graph with `n + 1` nodes, `T` has `n` arcs.) -/
def IsTreeSolution {n m : ℕ} (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (bsupply : Fin (n + 1) → ℝ) (f : Fin m → ℝ) : Prop :=
  ∃ T : Finset (Fin m), IsTreeArcSet arcs T ∧ (∀ k, k ∉ T → f k = 0) ∧
    (truncatedIncidence arcs).mulVec f = truncatedSupply bsupply

/-- **Bertsimas & Tsitsiklis, Definition 7.1 (p. 280).** A feasible tree solution: a tree
solution with `f ≥ 0`. -/
def IsFeasibleTreeSolution {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1)) (bsupply : Fin (n + 1) → ℝ)
    (f : Fin m → ℝ) : Prop :=
  IsTreeSolution arcs bsupply f ∧ 0 ≤ f

end LinearOptimization


