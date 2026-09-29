-- Prove2me | Theorems.Thm_MetricTSP_christofides_tour
-- name    : MetricTSP.christofides_tour
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T21:30:51.622857+00:00
-- url     : https://prove2.me/theorems/46373419-0c47-4992-ae46-afe89096ebc7
-- title:
--   Christofides against the LP: a tour within 3/2 of any Held--Karp objective
-- statement:
--   For every feasible point $x$ of the subtour-elimination (Held--Karp) relaxation on $n \ge 3$ cities with metric costs there is a Hamiltonian tour of cost at most $\tfrac32$ times the LP objective of $x$:
--   $$\exists\,\pi:\quad \mathrm{tourCost}(c,\pi) \;\le\; \tfrac32\cdot\tfrac12\sum_u\sum_v c(u,v)\,x_{uv}.$$
--
--   This is Wolsey's pointwise form of the Christofides analysis, run against the LP instead of against the optimum. It combines the two halves: (i) a connected spanning subgraph of cost at most the LP objective (`MetricTSP.cheap_connected_subgraph`, the fractional spanning-tree bound), and (ii) a perfect matching on the even set $T$ of odd-degree vertices of that subgraph of cost at most half the LP objective (`MetricTSP.parity_matching`, the T-join polyhedron half). Adding the matching to the subgraph makes every degree even while keeping it connected, so an Euler tour exists, and shortcutting it with the triangle inequality (`MetricTSP.tour_of_parity_join`) yields a Hamiltonian tour of cost at most $\mathrm{LP} + \tfrac12\,\mathrm{LP}$.
--
--   Taking the infimum over feasible $x$ gives Wolsey's bound $\mathrm{OPT} \le \tfrac32\,\mathrm{LP}$ for the Held--Karp relaxation.
-- source:
--   L. A. Wolsey, Heuristic analysis, linear programming and branch and bound, Mathematical Programming Study 13 (1980) 121-134, https://doi.org/10.1007/BFb0120913 (Section 3); D. B. Shmoys, D. P. Williamson, Analyzing the Held-Karp TSP bound: a monotonicity property with application, Information Processing Letters 35 (1990) 281-285, https://doi.org/10.1016/0020-0190(90)90028-V; N. Christofides, Worst-case analysis of a new heuristic for the travelling salesman problem, Report 388, GSIA, Carnegie Mellon University, 1976.

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem christofides_tour (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x) :
    ∃ π : Equiv.Perm (Fin n),
      tourCost c π ≤ (3 / 2) * ((1 / 2) * ∑ u, ∑ v, c u v * x u v) := by sorry

end MetricTSP
