-- Prove2me | Theorems.Thm_KServer_offlineCost_le_workFn
-- name    : KServer.offlineCost_le_workFn
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T05:43:45.214091+00:00
-- url     : https://prove2.me/theorems/513449b7-1c1f-4db3-8377-212bafa377cc
-- title:
--   The optimal offline cost is below every work-function value
-- statement:
--   For every configuration $X$,
--   $$\mathrm{OPT}(C_0,\sigma)\;\le\;w(C_0;\sigma;X).$$
--
--   **Role.** The work function refines the optimal offline cost by recording where the optimum ends up, and this inequality is the link back: constraining the endpoint can only make the offline problem harder. It is what converts a bound stated in terms of work-function values — the form every analysis of the Work Function Algorithm produces — into a bound against $\mathrm{OPT}$, which is what competitiveness is about. Taking the infimum over $X$ turns the inequality into an equality, so no information is lost in passing from $\mathrm{OPT}$ to $w$.
--
--   **Formalization Note** Both sides are infima over sets of schedule costs; the point is that every schedule contributing to the right-hand side contributes its own movement, without the final repositioning move, to the left-hand side, and that this final move is nonnegative.
-- source:
--   E. Koutsoupias, The k-server problem (survey), Computer Science Review 3 (2009) 105-118, https://doi.org/10.1016/j.cosrev.2009.04.002, Section 3.3, equation (4) and the remark that the work function refines the optimal offline cost (the optimum is recovered by minimising w_t over configurations); originally E. Koutsoupias, C. Papadimitriou, On the k-server conjecture, J. ACM 42(5) (1995) 971-983, https://doi.org/10.1145/210118.210128.

import Mathlib
import Definitions.Def_KServer_workfunction

namespace KServer

theorem offlineCost_le_workFn (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (X : Config k M) :
    offlineCost C₀ σ ≤ workFn C₀ σ X := by sorry

end KServer
