-- Prove2me | Theorems.Thm_KServer_workFn_approx_offlineCost
-- name    : KServer.workFn_approx_offlineCost
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T06:02:41.459595+00:00
-- url     : https://prove2.me/theorems/1df03c6a-d837-41c1-adaa-3bd15ae46967
-- title:
--   The optimal offline cost is the infimum of the work function
-- statement:
--   For every $\varepsilon>0$ there is a configuration $X$ with
--   $$w(C_0;\sigma;X)\;\le\;\mathrm{OPT}(C_0,\sigma)+\varepsilon.$$
--
--   **Role.** Together with the companion bound $\mathrm{OPT}\le w(X)$, valid for every $X$, this says that the optimal offline cost is exactly the infimum of the work function over configurations:
--   $$\mathrm{OPT}(C_0,\sigma)\;=\;\inf_X w(C_0;\sigma;X).$$
--   So the work function loses no information: it refines $\mathrm{OPT}$ by recording where an optimal solution ends up, and minimising that record recovers $\mathrm{OPT}$ itself. This is the direction that lets an argument phrased in terms of work-function values be cashed in against the optimum, and it is what justifies thinking of $w_t$ as "the cost of the optimal algorithm, resolved by endpoint".
--
--   The approximation is by $\varepsilon$ rather than exact because on a general metric space the offline optimum need not be attained by any schedule; where it is attained — on a finite metric space, for instance — the statement holds with $\varepsilon=0$ and the infimum over $X$ is a minimum.
--
--   **Formalization Note** The witness is the endpoint of a schedule whose cost is within $\varepsilon$ of the infimum: for that particular $X$ the final repositioning move of the work function is from the schedule's last configuration to itself, and so costs nothing.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, equation (4) and the remark that minimising the work function over configurations recovers the optimal offline cost; originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem workFn_approx_offlineCost (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (ε : ℝ) (hε : 0 < ε) :
    ∃ X : Config k M, workFn C₀ σ X ≤ offlineCost C₀ σ + ε := by sorry

end KServer
