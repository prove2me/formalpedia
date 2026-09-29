-- Prove2me | Theorems.Thm_WorstCaseVaR_Entropy_inf_dual_over_lambda0
-- name    : WorstCaseVaR.Entropy.inf_dual_over_lambda0
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:19:06.346985+00:00
-- url     : https://prove2.me/theorems/ca2809f1-ef71-4f63-a709-1b7d4e90830c
-- title:
--   Eq. (48), p. 554 — minimising the dual function over λ₀
-- statement:
--   Let $d \in \mathbb R$, $\lambda > 0$ and $0 \le \phi \le 1$. Then the function
--   $$\lambda_0 \mapsto \lambda_0 + \lambda d + \lambda e^{-\lambda_0/\lambda - 1}\big((e^{1/\lambda} - 1)\phi + 1\big), \qquad \lambda_0 \in \mathbb R,$$
--   attains its minimum, and
--   $$\min_{\lambda_0 \in \mathbb R} \Big(\lambda_0 + \lambda d + \lambda e^{-\lambda_0/\lambda - 1}\big((e^{1/\lambda} - 1)\phi + 1\big)\Big) = \lambda d + \lambda \log\big((e^{1/\lambda} - 1)\phi + 1\big).$$
--
--   With $\phi = \phi(\gamma)$ this is Eq. (48): it eliminates the multiplier of the normalisation constraint from the dual problem, leaving a one-dimensional minimisation over $\lambda > 0$.
--
--   **Formalization Note** The paper writes $\inf$; the infimum is attained, and the Lean statement (`IsLeast` of the range) says so.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 554, proof of Theorem 9, Eq. (48)

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- Eq. (48), p. 554: for `λ > 0` and `0 ≤ φ ≤ 1`, the infimum over `λ₀ ∈ ℝ` of
`θ(λ₀, λ) = λ₀ + λd + λe^{-λ₀/λ-1}((e^{1/λ} - 1)φ + 1)` is `λd + λ log((e^{1/λ} - 1)φ + 1)`,
and it is attained. -/
theorem inf_dual_over_lambda0 (d φ lam : ℝ) (hlam : 0 < lam) (hφ0 : 0 ≤ φ) (hφ1 : φ ≤ 1) :
    IsLeast
      (Set.range fun lam0 : ℝ =>
        lam0 + lam * d + lam * Real.exp (-(lam0 / lam) - 1) * ((Real.exp (1 / lam) - 1) * φ + 1))
      (dualValue d φ lam) := by sorry

end WorstCaseVaR.Entropy
