-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_high_probability_lower_bound
-- name    : BanditAlgorithm.bandit_high_probability_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-19T18:23:14.587988+00:00
-- url     : https://prove2.me/theorems/2b808105-35d4-4001-af09-3def83af3917
-- statement:
--   (High-probability lower bound, stochastic) Suppose a policy $\pi$ satisfies
--
--   $$R_n(\pi,\nu) \le B\sqrt{(k-1)n}$$
--
--   for all $\nu \in \mathcal{E}^k$ (Gaussian bandits with suboptimality gaps at most 1). Then for every $\delta$ there exists a bandit $\nu$ in the class with
--
--   $$\mathbb{P}\left(\bar R_n \ge \frac{1}{4}\min\Big\{n,\ \frac{1}{B}\sqrt{(k-1)n}\,\log\frac{1}{4\delta}\Big\}\right) \ge \delta$$
--
--   — expected-regret optimality forces heavy tails on the random regret.
-- source:
--   L&S Theorem 17.1, p.216

import Definitions.Def_banditRegret
import Definitions.Def_GaussianBandit


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_high_probability_lower_bound {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n)
    {B : ℝ} (hB : 0 < B) (π : BanditPolicy k)
    (hbound : ∀ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) →
      banditRegret (gaussianBandit μvec) π n ≤ B * Real.sqrt (((k : ℝ) - 1) * n))
    {δ : ℝ} (hδ : δ ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) ∧
      δ ≤ (banditMeasure (gaussianBandit μvec) π n).real
        {h | (1 / 4 : ℝ) * min (n : ℝ)
              (Real.sqrt (((k : ℝ) - 1) * n) * Real.log (1 / (4 * δ)) / B) ≤
            ∑ i, (armPullCount i h : ℝ) * banditGap (gaussianBandit μvec) i} := by
  sorry
