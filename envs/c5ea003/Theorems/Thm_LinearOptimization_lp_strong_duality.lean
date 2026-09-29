-- Prove2me | Theorems.Thm_LinearOptimization_lp_strong_duality
-- name    : LinearOptimization.lp_strong_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:51:52.476057+00:00
-- url     : https://prove2.me/theorems/a787879b-101e-4ee9-9a25-e863f5e67eb5
-- title:
--   Strong duality
-- statement:
--   **(Theorem 4.4, strong duality, GOAL)** If a linear programming problem has an optimal solution, so does its dual, and the respective optimal costs are equal.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.4, p. 148

import Definitions.Def_LinearOptimization_DualLP


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.4 (p. 148).** Strong duality, attainment form: if the
general-form primal has an optimal solution `x`, then its dual has an
optimal solution `p`, and the optimal costs agree: `p'b = c'x`. -/

theorem LinearOptimization.lp_strong_duality {m n : ℕ} (P : GeneralFormLP m n)
    (x : Fin n → ℝ) (hx : IsLpOptimal P.c (generalFeasibleSet P) x) :
    ∃ p : Fin m → ℝ,
      IsLpDualOptimal P.b (generalFeasibleSet (dualLP P)) p ∧
      p ⬝ᵥ P.b = P.c ⬝ᵥ x := by
  sorry
