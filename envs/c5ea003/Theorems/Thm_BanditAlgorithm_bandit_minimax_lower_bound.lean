-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_minimax_lower_bound
-- name    : BanditAlgorithm.bandit_minimax_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-19T18:22:09.00161+00:00
-- url     : https://prove2.me/theorems/d25ba630-2d54-43e9-bc88-05f62d074f84
-- statement:
--   (Minimax lower bound, GOAL) Let $k > 1$ and $n \ge k-1$. For any policy $\pi$ there exists a mean vector $\mu \in [0,1]^k$ such that on the unit-variance Gaussian bandit $\nu_\mu$,
--
--   $$R_n(\pi, \nu_\mu) \ge \frac{1}{27}\sqrt{(k-1)n}.$$
-- source:
--   L&S Theorem 15.2, p.199 (statement announced as Theorem 13.1, p.180)

import Definitions.Def_banditRegret
import Definitions.Def_GaussianBandit


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bandit_minimax_lower_bound {k n : ℕ} (hk : 1 < k) (hn : k - 1 ≤ n)
    (π : BanditPolicy k) :
    ∃ μvec : Fin k → ℝ, (∀ i, μvec i ∈ Set.Icc (0 : ℝ) 1) ∧
      Real.sqrt (((k : ℝ) - 1) * n) / 27 ≤
        banditRegret (gaussianBandit μvec) π n := by
  sorry
