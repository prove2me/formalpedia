-- Prove2me | Theorems.Thm_BanditAlgorithm_best_arm_identification_sample_complexity_lower_bound
-- name    : BanditAlgorithm.best_arm_identification_sample_complexity_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-30T03:28:31.565296+00:00
-- url     : https://prove2.me/theorems/9b9524da-f5b8-4c66-b106-310e98be3263
-- statement:
--   (Sample-complexity lower bound, Theorem 33.5) Let $\mathcal{E}$ be an arbitrary class of $k$-armed bandits and suppose $(\pi,\tau,\psi)$ is sound for $\mathcal{E}$ at confidence level $\delta\in(0,1)$, where $\tau$ is a stopping time of the natural filtration and $\psi$ is $\mathcal{F}_\tau$-measurable. Then for every $\nu\in\mathcal{E}$:
--
--   $$\mathbb{E}_{\nu\pi}[\tau] \ge c^*(\nu)\log\frac{1}{4\delta}$$
--
--   (stated in $[0,\infty]$, so no integrability side conditions).
-- source:
--   L&S Theorem 33.5, p.407

import Definitions.Def_BanditTrajectory


open MeasureTheory ProbabilityTheory ENNReal

theorem BanditAlgorithm.best_arm_identification_sample_complexity_lower_bound {k : ℕ}
    (𝓔 : Set (StochasticBandit k)) (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (π : BanditPolicy k) (τ : (ℕ → Fin k × ℝ) → ℕ∞) (ψ : (ℕ → Fin k × ℝ) → Fin k)
    (hτ : IsBanditStoppingTime τ) (hψ : Measurable[hτ.measurableSpace] ψ)
    (hsound : IsSoundBAI δ π τ ψ 𝓔) (ν : StochasticBandit k) (hν : ν ∈ 𝓔) :
    baiComplexity ν 𝓔 * ENNReal.ofReal (Real.log (1 / (4 * δ))) ≤
      ∫⁻ ω, (τ ω : ℝ≥0∞) ∂banditTrajMeasure ν π := by
  sorry
