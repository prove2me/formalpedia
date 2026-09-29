-- Prove2me | Theorems.Thm_WorstCaseVaR_Entropy_dual_function_closed_form
-- name    : WorstCaseVaR.Entropy.dual_function_closed_form
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:18:36.569479+00:00
-- url     : https://prove2.me/theorems/974b572e-7599-4392-b281-efe1995bc1e1
-- title:
--   Eq. (47), p. 554 — the tilted density maximises the Lagrangian; closed form of θ(λ₀, λ)
-- statement:
--   Let $P_0 = \mathcal N(\hat x, \Gamma)$ with $\Gamma \succ 0$, let $w \in \mathbb R^n$, $\gamma, d, \lambda_0 \in \mathbb R$ and $\lambda > 0$, and write $\mathcal S = \{x : \gamma \le -x^\top w\}$ with indicator $\chi_{\mathcal S}$. Call a measure $Q$ on $\mathbb R^n$ *admissible* if it is finite, $Q \ll P_0$, and $\log\frac{dQ}{dP_0}$ is $Q$-integrable (a density of finite relative entropy). For admissible $Q$ define the Lagrangian
--   $$L(Q) = Q(\mathcal S) + \lambda_0\big(1 - Q(\mathbb R^n)\big) + \lambda\Big(d - \int \log\frac{dQ}{dP_0}\,dQ\Big).$$
--   Let $Q^\star$ be the measure with density $\dfrac{dQ^\star}{dP_0}(x) = \exp\!\Big(\dfrac{\chi_{\mathcal S}(x) - \lambda_0}{\lambda} - 1\Big)$ (Eq. 47), and
--   $$\theta(\lambda_0,\lambda) = \lambda_0 + \lambda d + \lambda e^{-\lambda_0/\lambda - 1}\big((e^{1/\lambda} - 1)P_0(\mathcal S) + 1\big).$$
--   Then:
--   1. $Q^\star$ is admissible and $L(Q^\star) = \theta(\lambda_0,\lambda)$;
--   2. $L(Q) \le \theta(\lambda_0,\lambda)$ for every admissible $Q$;
--   3. $\lambda_0 + \lambda d + \lambda \displaystyle\int \exp\!\Big(\frac{\chi_{\mathcal S}(x) - \lambda_0}{\lambda} - 1\Big)\,dP_0(x) = \theta(\lambda_0,\lambda)$.
--
--   So the dual function $\theta(\lambda_0,\lambda) = \sup_Q L(Q)$ of the worst-case probability problem (46) is attained at the exponentially tilted density (47) and has the stated closed form.
--
--   **Formalization Note** The paper writes densities $p, p_0$; here $Q$ is a finite measure and $\log\frac{dQ}{dP_0}$ is Mathlib's log-likelihood ratio `llr Q P₀`. The paper's second line splits the integral over $\{\gamma \le -x^\top w\}$ and $\{\gamma \ge -x^\top w\}$, which overlap on a hyperplane; the Lean statement uses $P_0(\mathcal S)$ and its complement directly, so no null-set argument is needed.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 554, proof of Theorem 9, Eq. (47) and the display following it

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

open MeasureTheory

namespace WorstCaseVaR.Entropy

/-- Eq. (47) and the closed form of the dual function, p. 554. Fix `λ > 0` and `λ₀ ∈ ℝ`, and
let `𝒮 = {x | γ ≤ -xᵀw}`. Over finite measures `Q ≪ P₀` with `P₀`-log-likelihood ratio
integrable against `Q` (densities `p` of finite relative entropy), the Lagrangian
`L(Q) = Q(𝒮) + λ₀(1 - Q(ℝⁿ)) + λ(d - ∫ log(dQ/dP₀) dQ)` is maximised by the tilted measure
`dQ*/dP₀ = exp((χ_𝒮 - λ₀)/λ - 1)`, and its maximum is
`λ₀ + λd + λ∫ exp((χ_𝒮 - λ₀)/λ - 1) dP₀ = λ₀ + λd + λe^{-λ₀/λ-1}((e^{1/λ} - 1)P₀(𝒮) + 1)`. -/
theorem dual_function_closed_form {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (d γ lam0 lam : ℝ) (hlam : 0 < lam) :
    let P₀ := refGaussian xhat Γ
    let S := lossSet w γ
    let L : Measure (Returns n) → ℝ := fun Q =>
      Q.real S + lam0 * (1 - Q.real Set.univ) + lam * (d - ∫ x, llr Q P₀ x ∂Q)
    let Admissible : Measure (Returns n) → Prop := fun Q =>
      IsFiniteMeasure Q ∧ Q ≪ P₀ ∧ Integrable (llr Q P₀) Q
    let Qstar : Measure (Returns n) :=
      P₀.withDensity fun x => ENNReal.ofReal (Real.exp ((S.indicator 1 x - lam0) / lam - 1))
    let θ : ℝ := lam0 + lam * d +
      lam * Real.exp (-(lam0 / lam) - 1) * ((Real.exp (1 / lam) - 1) * P₀.real S + 1)
    Admissible Qstar ∧ L Qstar = θ ∧ (∀ Q, Admissible Q → L Q ≤ θ) ∧
      lam0 + lam * d + lam * ∫ x, Real.exp ((S.indicator 1 x - lam0) / lam - 1) ∂P₀ = θ := by sorry

end WorstCaseVaR.Entropy
