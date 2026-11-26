-- Prove2me | Theorems.Thm_MetricTSP_fractional_join_pairing
-- name    : MetricTSP.fractional_join_pairing
-- status  : Proved
-- author  : @domodus
-- created : 2026-11-26T19:41:44.806808+00:00
-- url     : https://prove2.me/theorems/0869b6a6-d77a-4178-8d8e-e8d5f1d70919
-- title:
--   Edmonds–Johnson: a pairing of $T$ no costlier than any fractional $T$-join
-- statement:
--   Let $c$ be a metric cost on $n$ cities, let $T$ be a set of cities of even cardinality, and let $y$ be a symmetric nonnegative weighting of the city pairs that covers every $T$-odd cut:
--   $$\sum_{u \in S}\sum_{v \notin S} y_{uv} \;\ge\; 1 \qquad \text{for every set } S \text{ of cities with } |S \cap T| \text{ odd}.$$
--   Then there is a perfect matching $M$ of $T$, encoded as a fixed-point-free involution $f$ of $T$ extended by the identity outside $T$, with
--   $$\sum_{v \in T} c(v, f(v)) \;\le\; \sum_u\sum_v c(u,v)\,y_{uv}.$$
--   Both sides count each pair twice, so this says $\mathrm{cost}(M) \le \sum_{e} c_e\,y_e$.
--
--   This is the Edmonds–Johnson description of the $T$-join polyhedron on the complete graph: for nonnegative costs the minimum of $c \cdot y$ over the cut constraints above is attained at a $T$-join. A $T$-join splits into $|T|/2$ paths pairing up $T$ (plus cycles), and the triangle inequality shortcuts each path to a single matching edge.
--
--   With $y = x/2$ for a Held–Karp point $x$ this is Wolsey's parity bound (`MetricTSP.parity_matching`). For general $y$ it is the step that turns the fractional $O$-join of Karlin, Klein and Oveis Gharan into an actual matching.
-- source:
--   J. Edmonds, E. L. Johnson, Matching, Euler tours and the Chinese postman, Math. Programming 5 (1973) 88-124; as used in A. Karlin, N. Klein, S. Oveis Gharan, arXiv:2105.10043v3, Proposition 2.4, p. 7; see also Cook, Cunningham, Pulleyblank, Schrijver, Combinatorial Optimization (1998), Theorem 5.28

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem fractional_join_pairing (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (T : Finset (Fin n)) (hT : Even T.card)
    (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u) (hnn : ∀ u v, 0 ≤ y u v)
    (hcut : ∀ S : Finset (Fin n), Odd (S ∩ T).card → 1 ≤ ∑ u ∈ S, ∑ v ∈ Sᶜ, y u v) :
    ∃ f : Fin n → Fin n, (∀ v ∈ T, f v ∈ T ∧ f (f v) = v ∧ f v ≠ v) ∧
      (∀ v ∉ T, f v = v) ∧
      ∑ v ∈ T, c v (f v) ≤ ∑ u, ∑ v, c u v * y u v := by sorry

end MetricTSP
