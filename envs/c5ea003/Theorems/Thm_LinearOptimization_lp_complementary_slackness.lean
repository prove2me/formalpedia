-- Prove2me | Theorems.Thm_LinearOptimization_lp_complementary_slackness
-- name    : LinearOptimization.lp_complementary_slackness
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T17:52:05.381543+00:00
-- url     : https://prove2.me/theorems/bef35675-6080-45f1-aa80-89c7200d2c56
-- title:
--   Complementary slackness
-- statement:
--   **(Theorem 4.5, complementary slackness)** Let $x$ and $p$ be feasible solutions to the primal and the dual problem, respectively. The vectors $x$ and $p$ are optimal solutions for the two respective problems if and only if:
--
--   - $p_i(a_i'x - b_i) = 0$ for all $i$, and
--   - $(c_j - p'A_j)x_j = 0$ for all $j$.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 4.5, p. 151

import Definitions.Def_LinearOptimization_DualLP


open Matrix

/-- **Bertsimas & Tsitsiklis, Theorem 4.5 (p. 151).** Complementary slackness: feasible `x`
and `p` are simultaneously optimal iff `pᵢ(aᵢ'x − bᵢ) = 0` for every
constraint `i` and `(cⱼ − p'Aⱼ)xⱼ = 0` for every variable `j`. -/

theorem LinearOptimization.lp_complementary_slackness {m n : ℕ} (P : GeneralFormLP m n)
    (x : Fin n → ℝ) (hx : x ∈ generalFeasibleSet P)
    (p : Fin m → ℝ) (hp : p ∈ generalFeasibleSet (dualLP P)) :
    (IsLpOptimal P.c (generalFeasibleSet P) x ∧
      IsLpDualOptimal P.b (generalFeasibleSet (dualLP P)) p) ↔
    ((∀ i, p i * (P.A i ⬝ᵥ x - P.b i) = 0) ∧
      ∀ j, (P.c j - p ⬝ᵥ (fun i => P.A i j)) * x j = 0) := by
  sorry
