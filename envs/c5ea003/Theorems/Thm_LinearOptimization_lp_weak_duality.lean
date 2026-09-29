-- Prove2me | Theorems.Thm_LinearOptimization_lp_weak_duality
-- name    : LinearOptimization.lp_weak_duality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:51:16.800044+00:00
-- url     : https://prove2.me/theorems/74b63290-8639-40be-995d-3db32e8372c0
-- title:
--   Weak duality
-- statement:
--   **(Theorem 4.3, weak duality)** If $x$ is a feasible solution to the primal problem and $p$ is a feasible solution to the dual problem, then
--
--   $$p'b \le c'x.$$
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.3, p. 146

import Definitions.Def_LinearOptimization_DualLP


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.3 (p. 146).** Weak duality for the general-form
primal/dual pair: any primal-feasible `x` and dual-feasible `p` satisfy
`p'b ≤ c'x`. -/

theorem LinearOptimization.lp_weak_duality {m n : ℕ} (P : GeneralFormLP m n)
    (x : Fin n → ℝ) (hx : x ∈ generalFeasibleSet P)
    (p : Fin m → ℝ) (hp : p ∈ generalFeasibleSet (dualLP P)) :
    p ⬝ᵥ P.b ≤ P.c ⬝ᵥ x := by
  sorry
