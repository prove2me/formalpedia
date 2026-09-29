-- Prove2me | Theorems.Thm_LinearOptimization_lp_optimal_certificate
-- name    : LinearOptimization.lp_optimal_certificate
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:51:40.635359+00:00
-- url     : https://prove2.me/theorems/f6ce170f-a816-41e9-a054-6a41cfb22b16
-- title:
--   Zero duality gap certifies optimality
-- statement:
--   **(Corollary 4.2)** Let $x$ and $p$ be feasible solutions to the primal and the dual, respectively, and suppose that
--
--   $$p'b = c'x.$$
--
--   Then, $x$ and $p$ are optimal solutions to the primal and the dual, respectively.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Corollary 4.2, p. 148

import Definitions.Def_LinearOptimization_DualLP


open Matrix

/-- **Bertsimas & Tsitsiklis, Corollary 4.2 (p. 148).** Feasible `x` and `p` with
`p'b = c'x` are automatically optimal for the primal and the dual,
respectively. -/

theorem LinearOptimization.lp_optimal_certificate {m n : ℕ} (P : GeneralFormLP m n)
    (x : Fin n → ℝ) (hx : x ∈ generalFeasibleSet P)
    (p : Fin m → ℝ) (hp : p ∈ generalFeasibleSet (dualLP P))
    (heq : p ⬝ᵥ P.b = P.c ⬝ᵥ x) :
    IsLpOptimal P.c (generalFeasibleSet P) x ∧
    IsLpDualOptimal P.b (generalFeasibleSet (dualLP P)) p := by
  sorry
