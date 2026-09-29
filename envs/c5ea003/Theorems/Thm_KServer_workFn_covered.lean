-- Prove2me | Theorems.Thm_KServer_workFn_covered
-- name    : KServer.workFn_covered
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:18:11.896738+00:00
-- url     : https://prove2.me/theorems/8926ccff-4de1-4416-a8d2-1e65eac54cec
-- title:
--   A request already covered by the target configuration is free
-- statement:
--   If the target configuration $X$ already has a server on the request $r$, then serving $r$ is free:
--   $$w(C_0;\sigma\cdot r;X)\;=\;w(C_0;\sigma;X).$$
--
--   **Role.** This is the first case of the recurrence that makes work functions computable by dynamic programming: when an optimal solution is already at the request, there is no additional cost to service it. Together with the other case — that otherwise some server moves from a point of $X$ onto $r$ — it determines $w_t$ from $w_{t-1}$ completely. The inequality $\ge$ is monotonicity in time; the inequality $\le$ holds because a schedule ending at $X$ can be extended by a step that stays at $X$, which serves $r$ at no cost.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, the properties of work functions listed after equation (4) (property 1, first case); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_covered (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (X : Config k M) (hX : ∃ i, X i = r) :
    workFn C₀ (σ ++ [r]) X = workFn C₀ σ X := by sorry

end KServer
