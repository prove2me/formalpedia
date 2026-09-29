-- Prove2me | Theorems.Thm_LinearOptimization_lp_unbounded_dual_infeasible
-- name    : LinearOptimization.lp_unbounded_dual_infeasible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:51:28.914829+00:00
-- url     : https://prove2.me/theorems/4d0b6767-62f2-4eed-91e1-590289a562bb
-- title:
--   An unbounded primal has an infeasible dual
-- statement:
--   **(Corollary 4.1)**
--
--   - **(a)** If the optimal cost in the primal is $-\infty$, then the dual problem must be infeasible.
--   - **(b)** If the optimal cost in the dual is $+\infty$, then the primal problem must be infeasible.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 4.1, p. 147

import Definitions.Def_LinearOptimization_DualLP


/-- **Bertsimas & Tsitsiklis, Corollary 4.1 (p. 147).** (a) A primal with optimal cost `−∞`
has an infeasible dual; (b) a dual with optimal cost `+∞` has an
infeasible primal. -/

theorem LinearOptimization.lp_unbounded_dual_infeasible {m n : ℕ} (P : GeneralFormLP m n) :
    (lpValue P.c (generalFeasibleSet P) = ⊥ →
      generalFeasibleSet (dualLP P) = ∅) ∧
    (lpDualValue P.b (generalFeasibleSet (dualLP P)) = ⊤ →
      generalFeasibleSet P = ∅) := by
  sorry
