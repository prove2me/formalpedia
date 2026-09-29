-- Prove2me | Theorems.Thm_MetricTSP_even_set_matching
-- name    : MetricTSP.even_set_matching
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T22:44:28.255776+00:00
-- url     : https://prove2.me/theorems/b67141fd-c8a6-4fde-b72c-d0cc0045d877
-- title:
--   A perfect matching within any fractional matching on an even set
-- statement:
--   Let $W$ be a nonempty set of cities of even cardinality, $c$ a metric cost, and $y$ a **fractional perfect matching** on $W$ satisfying all cut constraints: $y$ is symmetric, nonnegative, supported on $W$, with $\sum_u y(v,u) = 1$ for every $v \in W$, and $y(S, W \setminus S) \ge 1$ for every proper nonempty $S \subseteq W$. Then there is a (integral) perfect matching of $W$ — encoded as a fixed-point-free involution $f$ of $W$, the identity outside $W$ — whose (doubled) cost is at most the (doubled) cost of $y$:
--   $$\sum_{v \in W} c(v, f(v)) \;\le\; \sum_u \sum_v y(u,v)\, c(u,v).$$
--
--   This is an instance of **Edmonds' perfect matching polytope theorem**: the constraints imply the blossom (odd-cut) inequalities, so $y$ lies in the perfect matching polytope and dominates a convex combination of perfect matchings, one of which is no costlier than the average. The all-cuts form assumed here (rather than only odd cuts) is what the Held–Karp relaxation supplies, and it admits a self-contained inductive proof: by induction on $|W|$ and the support size, either a proper tight cut $y(\delta S) = 1$ exists — then the instance splits into two smaller contracted instances whose matchings glue across the single crossing unit — or no proper cut is tight, and the fractional support contains an even closed walk along which $y$ can be perturbed in both directions until the support shrinks or a cut becomes tight.
--
--   It is the final combinatorial ingredient of the parity-correction step (`MetricTSP.parity_matching`) in Wolsey's $\tfrac32$ analysis.
-- source:
--   J. Edmonds, Maximum matching and a polyhedron with 0,1-vertices, Journal of Research of the National Bureau of Standards 69B (1965) 125-130 (the matching polytope theorem); A. Schrijver, Combinatorial Optimization: Polyhedra and Efficiency, Springer 2003, Chapter 25 (perfect matching polytope, tight-cut decomposition proof).

import Mathlib
import Definitions.Def_MetricTSP_model

namespace MetricTSP

theorem even_set_matching (n : ℕ) (c : Fin n → Fin n → ℝ) (hc : IsMetricCost c)
    (W : Finset (Fin n)) (hW : Even W.card) (hWn : W.Nonempty)
    (y : Fin n → Fin n → ℝ) (hsym : ∀ u v, y u v = y v u)
    (hnn : ∀ u v, 0 ≤ y u v) (hdiag : ∀ v, y v v = 0)
    (hsupp : ∀ u v, y u v ≠ 0 → u ∈ W ∧ v ∈ W)
    (hdeg : ∀ v ∈ W, ∑ u, y v u = 1)
    (hcut : ∀ S : Finset (Fin n), S ⊆ W → S.Nonempty → S ≠ W →
      1 ≤ ∑ u ∈ S, ∑ v ∈ W \ S, y u v) :
    ∃ f : Fin n → Fin n, (∀ v ∈ W, f v ∈ W ∧ f (f v) = v ∧ f v ≠ v) ∧
      (∀ v ∉ W, f v = v) ∧
      ∑ v ∈ W, c v (f v) ≤ ∑ u, ∑ v, y u v * c u v := by sorry

end MetricTSP
