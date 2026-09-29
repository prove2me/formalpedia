-- Prove2me | Theorems.Thm_BanditAlgorithm_adversarial_bandit_exp3_regret_bound_basic
-- name    : BanditAlgorithm.adversarial_bandit_exp3_regret_bound_basic
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T23:27:54.20108+00:00
-- url     : https://prove2.me/theorems/4b189583-31e5-490c-bf1c-665f4e0c9b12
-- statement:
--   (Exp3, basic bound) Let $x \in [0,1]^{n\times k}$ with $k > 1$ arms and horizon $n \ge 1$, and let $\pi$ be Exp3 with learning rate $\eta = \sqrt{\log(k)/(nk)}$. Then
--
--   $$R_n(\pi, x) \le 2\sqrt{nk\log k}.$$
-- source:
--   L&S Theorem 11.1, p.153

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.adversarial_bandit_exp3_regret_bound_basic
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k)
    (hπ : IsExp3Policy (Real.sqrt (Real.log k / (n * k))) π) :
    adversarialRegret n x π ≤ 2 * Real.sqrt (n * k * Real.log k) := by
  sorry
