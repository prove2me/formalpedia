-- Prove2me | Theorems.Thm_WorstCaseVaR_Entropy_gaussian_tail_eq
-- name    : WorstCaseVaR.Entropy.gaussian_tail_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:18:01.17523+00:00
-- url     : https://prove2.me/theorems/984fb152-cce9-4a44-9915-59b495c903a8
-- title:
--   p. 554 — the Gaussian tail φ(γ) = 1 − Φ((γ + wᵀx̂)/√(wᵀΓw))
-- statement:
--   Let $P_0 = \mathcal N(\hat x, \Gamma)$ be a Gaussian distribution on $\mathbb R^n$ with positive definite covariance $\Gamma \succ 0$, let $w \in \mathbb R^n$ be nonzero and $\gamma \in \mathbb R$. Then the $P_0$-probability that the portfolio $w$ loses at least $\gamma$ is
--   $$\phi(\gamma) := P_0\{x : \gamma \le -x^\top w\} = 1 - \Phi\!\left(\frac{\gamma + w^\top \hat x}{\sqrt{w^\top \Gamma w}}\right),$$
--   where $\Phi$ is the standard normal cumulative distribution function.
--
--   This is the only place where the Gaussian reference distribution enters the proof of Theorem 9: the worst-case probability depends on $P_0$ only through $\phi(\gamma)$.
--
--   **Formalization Note** The probability is the real-valued measure `measureReal` of the loss set.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 554, proof of Theorem 9, display defining φ(γ)

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- p. 554: under the reference Gaussian `P₀ = 𝒩(x̂, Γ)` with `Γ ≻ 0` and `w ≠ 0`,
`φ(γ) := Prob{γ ≤ -xᵀw} = 1 - Φ((γ + wᵀx̂)/√(wᵀΓw))`. -/
theorem gaussian_tail_eq {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (γ : ℝ) :
    (refGaussian xhat Γ).real (lossSet w γ) = gaussianTail xhat Γ w γ := by sorry

end WorstCaseVaR.Entropy
