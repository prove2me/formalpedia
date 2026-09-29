-- Prove2me | Theorems.Thm_MetricTSP_parity_matching
-- name    : MetricTSP.parity_matching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T21:30:50.971321+00:00
-- url     : https://prove2.me/theorems/0943da92-bedb-4710-bf75-d9b8200c8935
-- title:
--   The parity correction: a matching within half of any Held--Karp objective
-- statement:
--   For every feasible point $x$ of the Held--Karp relaxation on $n \ge 3$ cities with metric costs, and every set $T$ of cities of even cardinality, there is a perfect matching of the cities of $T$ (encoded as a fixed-point-free involution $f$ of $T$, extended by the identity outside $T$) whose cost is at most **half** the LP objective of $x$:
--   $$\sum_{\{u,v\} \in M} c(u,v) \;=\; \tfrac12\sum_{v \in T} c(v, f(v)) \;\le\; \tfrac12\cdot\Bigl(\tfrac12\sum_u\sum_v c(u,v)\,x_{uv}\Bigr).$$
--   (The formal statement is the doubled inequality $\sum_{v \in T} c(v,f(v)) \le \tfrac12\sum_u\sum_v c(u,v)x_{uv}$.)
--
--   This is the deep half of Wolsey's analysis of Christofides' algorithm against the LP. The classical proof goes through the **$T$-join polyhedron** of Edmonds and Johnson: $x/2$ satisfies all the $T$-cut constraints $y(\delta(S)) \ge 1$ (because $x(\delta(S)) \ge 2$ for every proper cut), and the $T$-join polyhedron has integral vertices, so some $T$-join --- hence, by the triangle inequality, some perfect matching on $T$ --- costs at most $c \cdot x/2$. Equivalent routes: Edmonds' perfect-matching polytope (blossom inequalities) applied to $x/2$ restricted and shortcut onto $T$, or the packing of $T$-joins in Eulerian multigraphs obtained by scaling a rational $x$ (Seymour-type packing via Lovász splitting-off).
--
--   Applied with $T$ the odd-degree vertices of a cheap connected subgraph it completes the bound $\mathrm{OPT} \le \tfrac32\,\mathrm{LP}$.
-- source:
--   J. Edmonds, E. L. Johnson, Matching, Euler tours and the Chinese postman, Mathematical Programming 5 (1973) 88-124, https://doi.org/10.1007/BF01580113 (the T-join polyhedron); L. A. Wolsey, Heuristic analysis, linear programming and branch and bound, Mathematical Programming Study 13 (1980) 121-134 (Section 3); D. B. Shmoys, D. P. Williamson, Analyzing the Held-Karp TSP bound: a monotonicity property with application, Information Processing Letters 35 (1990) 281-285.

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem parity_matching (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (x : Fin n → Fin n → ℝ) (hx : IsHeldKarp x)
    (T : Finset (Fin n)) (hT : Even T.card) :
    ∃ f : Fin n → Fin n, (∀ v ∈ T, f v ∈ T ∧ f (f v) = v ∧ f v ≠ v) ∧
      (∀ v ∉ T, f v = v) ∧
      ∑ v ∈ T, c v (f v) ≤ (1 / 2) * ∑ u, ∑ v, c u v * x u v := by sorry

end MetricTSP
