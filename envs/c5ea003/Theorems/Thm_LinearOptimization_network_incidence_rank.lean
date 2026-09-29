-- Prove2me | Theorems.Thm_LinearOptimization_network_incidence_rank
-- name    : LinearOptimization.network_incidence_rank
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T21:59:25.093096+00:00
-- url     : https://prove2.me/theorems/5f14dc4e-5e81-47b8-9172-3d82e89fe1ca
-- title:
--   Row independence of the truncated incidence matrix of a connected graph
-- statement:
--   **(Bertsimas & Tsitsiklis, Corollary 7.1, p. 282)** If the graph $G$ is connected, then the matrix $\tilde{\mathbf{A}}$ has linearly independent rows.
--
--   (Here $\tilde{\mathbf{A}}$ is the truncated node-arc incidence matrix of dimensions $(n-1)\times m$, consisting of the first $n-1$ rows of $\mathbf{A}$ — i.e., the redundant row of flow conservation at the last node $n$ is deleted, p. 280. Equivalently, $\mathrm{rank}\,\tilde{\mathbf{A}}=n-1$.)
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 7.1, p. 282

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_NetworkFlowProblem


open Matrix

/-- **Bertsimas & Tsitsiklis, Corollary 7.1 (p. 282).** For a connected graph on `n + 1`
nodes, the truncated node-arc incidence matrix `Ã` (last row deleted) has
linearly independent rows. -/

theorem LinearOptimization.network_incidence_rank {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (hloop : HasNoSelfLoops arcs) (hconn : IsConnectedNetwork arcs) :
    LinearIndependent ℝ (fun i => truncatedIncidence arcs i) := by
  sorry
