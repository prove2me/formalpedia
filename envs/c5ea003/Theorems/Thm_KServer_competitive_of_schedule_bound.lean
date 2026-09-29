-- Prove2me | Theorems.Thm_KServer_competitive_of_schedule_bound
-- name    : KServer.competitive_of_schedule_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T03:47:53.712689+00:00
-- url     : https://prove2.me/theorems/a156336b-4207-405f-90e3-4132ce1056a2
-- title:
--   Competitiveness follows from a bound against every offline schedule
-- statement:
--   Let $A$ be a deterministic online $k$-server algorithm on a metric space $M$, with $k\ge1$, and let $c\ge0$ and $a$ be constants. Suppose $A$ beats **every individual offline schedule** by the factor $c$ and the additive constant $a$: for every request sequence $\sigma$ and every schedule $S$ that starts at $A$'s initial configuration and serves $\sigma$,
--   $$\mathrm{cost}_A(\sigma)\;\le\;c\cdot\sum_{j} \mathrm{moveCost}\bigl(S_j,S_{j+1}\bigr)\;+\;a .$$
--
--   **Statement.** Then $A$ is $c$-competitive, that is, the same bound holds against the offline *optimum*:
--   $$\mathrm{cost}_A(\sigma)\;\le\;c\cdot\mathrm{OPT}\bigl(A(\varepsilon),\sigma\bigr)+a\qquad\text{for every }\sigma .$$
--
--   **Role.** This is the bridge every upper-bound proof in competitive analysis crosses, usually without comment. A potential-function argument never reasons about the optimum directly: it fixes one adversary trajectory and compares the online algorithm against it step by step. What that produces is the displayed per-schedule bound, and turning it into a statement about $\mathrm{OPT}$ means passing to an infimum — legitimate because the optimum is the *greatest* lower bound of the schedule costs, and because the set of schedules is nonempty. Stating it once as a standalone result lets each upper bound — the two-server case, spaces of $k+1$ and $k+2$ points, the line, and the Work Function Algorithm — do only the part that is specific to it.
--
--   **Formalization Note** `IsCompetitive A c` unfolds to $\exists a,\ \forall \sigma,\ \mathrm{cost}_A(\sigma)\le c\cdot\mathrm{offlineCost}(A(\varepsilon),\sigma)+a$, with the additive constant quantified before the request sequence; the constant supplied here is the same $a$. The hypothesis $c\ge0$ is what makes multiplying an infimum by $c$ preserve the inequality; the degenerate case $c=0$ is covered separately, using only that some schedule exists.
-- source:
--   Standard step in every competitive-analysis upper bound: potential-function arguments compare the online algorithm against a fixed adversary trajectory, and the resulting per-schedule bound is passed to the infimum defining the optimum. See E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 2 (definition of the competitive ratio with an additive constant), and Manasse--McGeoch--Sleator, Competitive algorithms for server problems, J. Algorithms 11 (1990) 208-230, https://doi.org/10.1016/0196-6774(90)90003-W, Section 2.

import Mathlib
import Definitions.Def_KServer_model

namespace KServer

theorem competitive_of_schedule_bound (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (A : OnlineAlgorithm k M) (c a : ℝ) (hc : 0 ≤ c)
    (h : ∀ (σ : List M) (S : ℕ → Config k M), ServesFrom (A.conf []) σ S →
      A.cost σ ≤ c * (∑ j ∈ Finset.range σ.length, moveCost (S j) (S (j + 1))) + a) :
    IsCompetitive A c := by sorry

end KServer
