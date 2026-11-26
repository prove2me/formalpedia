-- Prove2me | Theorems.Thm_MetricTSP_kkg_connected_graph_and_join
-- name    : MetricTSP.kkg_connected_graph_and_join
-- status  : Open
-- author  : @domodus
-- created : 2026-11-26T19:42:04.124045+00:00
-- url     : https://prove2.me/theorems/599bc1da-1873-4f88-ac8e-4e07d9c5cfdf
-- title:
--   KKG core: a connected graph plus a fractional parity join within $3/2 - \varepsilon$ of the LP
-- statement:
--   There is a constant $\varepsilon > 10^{-36}$ with the following property. Let $c$ be a metric cost on $n \ge 3$ cities and let $x$ be a feasible point of the subtour-elimination (Held–Karp) relaxation. Then there are a connected spanning graph $G$ and a fractional parity join $y$ for $G$ whose combined cost is at most $\tfrac32 - \varepsilon$ times the LP objective of $x$.
--
--   Write $O(G)$ for the set of odd-degree vertices of $G$. The vector $y$ is a symmetric nonnegative weighting of the city pairs that covers every $O(G)$-odd cut:
--   $$\sum_{u \in S}\sum_{v \notin S} y_{uv} \;\ge\; 1 \qquad \text{for every } S \text{ with } |S \cap O(G)| \text{ odd}.$$
--   The cost bound reads
--   $$\mathrm{cost}(G) + \tfrac12\sum_{u}\sum_{v} c(u,v)\,y_{uv} \;\le\; \Bigl(\tfrac32 - \varepsilon\Bigr)\cdot\tfrac12\sum_u\sum_v c(u,v)\,x_{uv},$$
--   where both double sums count each unordered pair twice.
--
--   This is the probabilistic core of Karlin, Klein and Oveis Gharan. They sample a spanning tree $T$ from the maximum-entropy distribution whose marginals are $x$ (after splitting one city so that the LP has an edge $e_0$ with $x_{e_0} = 1$ and $c(e_0) = 0$), so $\mathbb E[c(T \cup e_0)] = c(x)$. They then build a random vector $y$ that is feasible for the $O$-join polyhedron of $T \cup e_0$ (Proposition 2.4) with $\mathbb E[c(y)] \le (\tfrac12 - \varepsilon)\,c(x)$ (Section 6.2, from Theorem 6.1). Some outcome of the random experiment meets the expected bound. Contracting $e_0$ gives a connected multigraph on the original cities. Passing to its simple support drops a set $D$ of edges of even multiplicity; adding the indicator of $D$ to $y$ keeps every cut covered for the new odd set and does not raise the total cost.
--
--   The pointwise form (every feasible $x$, not only optimal or extreme ones) follows because the Held–Karp polytope is bounded, so $x$ is a convex combination of extreme points and one of them is at least as cheap.
-- source:
--   A. Karlin, N. Klein, S. Oveis Gharan, A (slightly) improved bound on the integrality gap of the subtour LP for TSP, FOCS 2022, arXiv:2105.10043v3, Section 2.1 (Algorithm 1, Fact 2.3), Proposition 2.4, Section 6.2 (proof of Theorem 1.1 from Theorem 6.1), pp. 5-7 and 36-37

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_graph_cost

namespace MetricTSP

open Classical in
theorem kkg_connected_graph_and_join :
    ∃ ε : ℝ, 1 / 10 ^ 36 < ε ∧
      ∀ (n : ℕ), 3 ≤ n → ∀ c : Fin n → Fin n → ℝ, IsMetricCost c →
      ∀ x : Fin n → Fin n → ℝ, IsHeldKarp x →
        ∃ (G : SimpleGraph (Fin n)) (y : Fin n → Fin n → ℝ), G.Connected ∧
          (∀ u v, y u v = y v u) ∧ (∀ u v, 0 ≤ y u v) ∧
          (∀ S : Finset (Fin n), Odd (S.filter fun v => Odd (G.degree v)).card →
            1 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, y u v) ∧
          graphCost c G + (1 / 2) * ∑ u, ∑ v, c u v * y u v ≤
            (3 / 2 - ε) * ((1 / 2) * ∑ u, ∑ v, c u v * x u v) := by sorry

end MetricTSP
