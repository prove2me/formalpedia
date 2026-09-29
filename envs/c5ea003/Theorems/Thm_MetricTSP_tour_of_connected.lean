-- Prove2me | Theorems.Thm_MetricTSP_tour_of_connected
-- name    : MetricTSP.tour_of_connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T19:55:39.076405+00:00
-- url     : https://prove2.me/theorems/c8cf870e-2e9e-45a6-953c-05224946b980
-- title:
--   Doubling a connected subgraph yields a tour of at most twice its cost
-- statement:
--   **Tree doubling / shortcutting.** If $G$ is a connected graph on the $n \ge 1$ cities and $c$ is a metric cost, there is a Hamiltonian tour of cost at most twice the total edge cost of $G$:
--   $$\exists\,\pi:\quad \mathrm{tourCost}(c, \pi) \;\le\; 2\sum_{e \in E(G)} c(e).$$
--
--   This is the classical double-tree construction: doubling the edges of a spanning tree of $G$ gives an Eulerian multigraph; traversing an Euler tour and shortcutting repeated cities with the triangle inequality gives a Hamiltonian cycle paying each tree edge at most twice. Equivalently — and this is how the inductive proof goes — grow the tour by inserting one new city at a time right after a neighbor already on the tour: inserting $w$ after $p$ replaces the edge $(p, s)$ by $(p, w), (w, s)$ and costs at most $2c(p,w)$ by the triangle inequality.
--
--   Applied to a minimum spanning tree this is the classical $2$-approximation for metric TSP; applied against the Held--Karp relaxation it gives the integrality-gap bound $\mathrm{OPT} \le 2\,\mathrm{LP}$.
-- source:
--   D. J. Rosenkrantz, R. E. Stearns, P. M. Lewis II, An analysis of several heuristics for the traveling salesman problem, SIAM Journal on Computing 6 (1977) 563-581, https://doi.org/10.1137/0206041 (Theorem 2, the nearest-insertion/double-tree 2-approximation); D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press 2011, Theorem 2.12 (the double-tree algorithm).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost

namespace MetricTSP

theorem tour_of_connected (n : ℕ) (hn : 1 ≤ n) (c : Fin n → Fin n → ℝ)
    (hc : IsMetricCost c) (G : SimpleGraph (Fin n)) (hG : G.Connected) :
    ∃ π : Equiv.Perm (Fin n), tourCost c π ≤ 2 * graphCost c G := by sorry

end MetricTSP
