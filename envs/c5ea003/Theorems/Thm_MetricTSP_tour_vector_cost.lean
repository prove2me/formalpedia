-- Prove2me | Theorems.Thm_MetricTSP_tour_vector_cost
-- name    : MetricTSP.tour_vector_cost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-24T19:21:01.495859+00:00
-- url     : https://prove2.me/theorems/2d8bc895-2a6b-44e0-a7be-d4f407cfc32b
-- title:
--   The LP objective of a tour vector is twice the tour cost
-- statement:
--   For $n \ge 3$ cities and any symmetric cost function $c$, the linear-programming objective of the incidence vector of a Hamiltonian tour equals twice the cost of that tour:
--   $$\sum_{u}\sum_{v} c(u,v)\, x^{\pi}_{uv} \;=\; 2\, \mathrm{tourCost}(c, \pi),$$
--   where $x^{\pi}$ is the tour's incidence vector. The ordered double sum counts every step of the tour twice --- once as $(u,v)$ and once as $(v,u)$ --- and the two contributions match by the symmetry of $c$. Combined with the feasibility of tour vectors, this identity shows that the Held--Karp value (which halves the double sum) is at most the optimal tour cost.
-- source:
--   M. Held, R. M. Karp, The traveling-salesman problem and minimum spanning trees, Operations Research 18 (1970) 1138-1162 (the Held--Karp bound is a lower bound on the tour cost); D. P. Williamson, D. B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press 2011, Section 11.2 (the subtour LP objective of a tour vector is the tour cost, stated with edge variables; here each edge is counted twice in the ordered double sum).

import Mathlib
import Definitions.Def_MetricTSP_model
import Definitions.Def_MetricTSP_tour_vector

namespace MetricTSP

theorem tour_vector_cost (n : ℕ) (hn : 3 ≤ n) (c : Fin n → Fin n → ℝ)
    (hsym : ∀ u v, c u v = c v u) (π : Equiv.Perm (Fin n)) :
    ∑ u, ∑ v, c u v * tourVec π u v = 2 * tourCost c π := by sorry

end MetricTSP
