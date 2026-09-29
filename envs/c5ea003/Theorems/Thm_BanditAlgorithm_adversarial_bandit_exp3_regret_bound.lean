-- Prove2me | Theorems.Thm_BanditAlgorithm_adversarial_bandit_exp3_regret_bound
-- name    : BanditAlgorithm.adversarial_bandit_exp3_regret_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-17T23:28:16.875433+00:00
-- url     : https://prove2.me/theorems/b1e1d077-58ee-4865-b65c-a7c2aa46f544
-- statement:
--   (Exp3, improved bound, GOAL) Let $x \in [0,1]^{n\times k}$ be an adversarial bandit with $k > 1$ arms and horizon $n \ge 1$, and let $\pi$ be Exp3 with learning rate $\eta = \sqrt{2\log(k)/(nk)}$. Then
--
--   $$R_n(\pi, x) \le \sqrt{2nk\log k}.$$
-- source:
--   L&S Theorem 11.2, p.156

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy


open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.adversarial_bandit_exp3_regret_bound
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k)
    (hπ : IsExp3Policy (Real.sqrt (2 * Real.log k / (n * k))) π) :
    adversarialRegret n x π ≤ Real.sqrt (2 * n * k * Real.log k) := by
  sorry
