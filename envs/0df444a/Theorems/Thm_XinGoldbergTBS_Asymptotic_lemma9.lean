-- Prove2me | Theorems.Thm_XinGoldbergTBS_Asymptotic_lemma9
-- name    : XinGoldbergTBS.Asymptotic.lemma9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T01:29:21.548183+00:00
-- url     : https://prove2.me/theorems/406742cf-c173-4645-86eb-6b19d83b4afd
-- title:
--   Lemma 9 — bounds on $\underline\xi_0, \bar\xi_0, \epsilon_0$ and $m_\alpha$
-- statement:
--   With $\underline\xi_0 = 2^{-\hat p_0^2/400}$, $\bar\xi_0 = 2^{-(4/(\hat p_0^2\eta_0^2))\epsilon_0^2}$ and $m_\alpha = \lceil -1/\log_2(\alpha)\rceil$:
--   1. $0.998 < \underline\xi_0 \le 1 - \epsilon_0 \le \bar\xi_0 < 1$;
--   2. $L \ge \epsilon_0^{-2}$ implies $\epsilon_0^{-3}L\exp(-\epsilon_0 L) \le 25$;
--   3. $\alpha \in [\underline\xi_0, \bar\xi_0]$ implies
--      - $m_\alpha, 2m_\alpha \in \big[400\hat p_0^{-2}, (\hat p_0\eta_0\epsilon_0^{-1})^2\big]$;
--      - $\tfrac14(1-\alpha)^{-1} \le m_\alpha \le 4(1-\alpha)^{-1}$.
--
--   These elementary estimates on the constants feed the proof of Corollary 4.
--
--   **Formalization Note** $L$ in 2 ranges over natural numbers (it is the regular lead time).
-- source:
--   Xin and Goldberg, Asymptotic Optimality of Tailored Base-Surge Policies in Dual-Sourcing Inventory Systems, Management Science 64(1), 2018, p. 450, Appendix A.3, Lemma 9

import Mathlib
import Definitions.Def_XinGoldbergTBS_Asymptotic_Model
import Definitions.Def_XinGoldbergTBS_Asymptotic_Constants

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators

namespace XinGoldbergTBS.Asymptotic

/-- Lemma 9, p. 450: bounds on `ξ̲₀ = 2^{-p̂₀²/400}`, `ξ̄₀ = 2^{-(4/(p̂₀²η₀²))ϵ₀²}`, `ϵ₀` and
`m_α = ⌈-1/log₂(α)⌉`. -/
theorem lemma9 (μ : DemandLaw) (κ : Costs) (L₀ : ℕ) :
    (0.998 < xiLow μ ∧ xiLow μ ≤ 1 - eps0 μ κ L₀ ∧
      1 - eps0 μ κ L₀ ≤ xiHigh μ κ L₀ ∧ xiHigh μ κ L₀ < 1) ∧
    (∀ L : ℕ, (eps0 μ κ L₀ ^ 2)⁻¹ ≤ (L : ℝ) →
      (eps0 μ κ L₀ ^ 3)⁻¹ * L * Real.exp (-(eps0 μ κ L₀ * L)) ≤ 25) ∧
    (∀ α : ℝ, xiLow μ ≤ α → α ≤ xiHigh μ κ L₀ →
      (400 * (p0hat μ ^ 2)⁻¹ ≤ (mAlpha α : ℝ) ∧
        (mAlpha α : ℝ) ≤ (p0hat μ * eta0 μ * (eps0 μ κ L₀)⁻¹) ^ 2 ∧
        400 * (p0hat μ ^ 2)⁻¹ ≤ 2 * (mAlpha α : ℝ) ∧
        2 * (mAlpha α : ℝ) ≤ (p0hat μ * eta0 μ * (eps0 μ κ L₀)⁻¹) ^ 2) ∧
      (1 / 4) * (1 - α)⁻¹ ≤ (mAlpha α : ℝ) ∧ (mAlpha α : ℝ) ≤ 4 * (1 - α)⁻¹) := by sorry

end XinGoldbergTBS.Asymptotic
