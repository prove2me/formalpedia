-- Prove2me | Theorems.Thm_MetricTSP_three_paths_opt_lower
-- name    : MetricTSP.three_paths_opt_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T20:12:56.002684+00:00
-- url     : https://prove2.me/theorems/33fc514e-cacc-4c15-8840-cdd036fbff92
-- title:
--   Every tour of the three-paths instance costs at least 4k+2
-- statement:
--   Every Hamiltonian tour of the three-parallel-paths instance costs at least $4k + 2$.
--
--   This is the combinatorial heart of the $4/3$ lower bound. Each step of a tour moves along a shortest route of the underlying graph, so a tour induces a usage count $x_{j,\ell}$ for each edge of the graph ($j$ the path, $\ell$ the level along it). The total tour cost is $\sum_{j,\ell} x_{j,\ell}$, and the usage counts inherit three properties from the closed tour: at every city the incident usages have even sum (the tour enters as often as it leaves) and positive sum (the city is visited); and no path can have two unused edges, since the segment strictly between them would be visited but every route into it crosses one of the two unused edges.
--
--   Consequently each path is either used with all-odd counts (total at least $k+1$) or with all-even counts and at most one zero (total at least $2k$), and the parity constraint at the hub $s$ forces an even number of odd paths: either two odd paths and one even path, at least $(k+1) + (k+1) + 2k = 4k + 2$, or three even paths, at least $6k$. Every tour therefore costs at least $4k+2$, while the LP value is at most $3k+3$ --- the ratio tends to $4/3$.
-- source:
--   M. X. Goemans, Worst-case comparison of valid inequalities for the TSP, Mathematical Programming 69 (1995) 335-349, Section 4 (the optimum of the three-path family is 4k + O(1)); D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, CUP 2011, Exercise 11.3 (the optimal tour of the family costs 4k + O(1) while the LP is 3k + O(1)).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_three_paths

namespace MetricTSP

theorem three_paths_opt_lower (k : ℕ) (hk : 2 ≤ k) :
    (4 * k + 2 : ℝ) ≤ tspOpt (tpCost k) := by sorry

end MetricTSP
