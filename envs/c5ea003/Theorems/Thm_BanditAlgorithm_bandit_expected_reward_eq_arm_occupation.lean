-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_expected_reward_eq_arm_occupation
-- name    : BanditAlgorithm.bandit_expected_reward_eq_arm_occupation
-- status  : Proved
-- author  : @MKPynnic
-- created : 2026-07-18T16:52:31.703706+00:00
-- url     : https://prove2.me/theorems/c0fc274e-869c-4e8d-8b87-61cd22fe08dd
-- title:
--   Expected reward by arm occupation
-- statement:
--   In the canonical finite-armed stochastic bandit model with integrable reward laws, expected cumulative reward equals the arm-mean-weighted expected occupation count:
--   $$\mathbb{E}\left[\sum_{t=1}^n X_t\right]=\sum_{i=1}^k \mu_i\,\mathbb{E}[T_i(n)]$$
--   This is the tower-property calculation in the proof of the regret decomposition lemma: conditional on selecting arm $i$, the reward has mean $\mu_i$, and finite sums then interchange rounds and arms. The statement includes horizon $n=0$ and does not require a positive number of arms.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Lemma 4.5, printed p. 63, Eq. (4.6) and the conditional-expectation display immediately following it, https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_banditRegret

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem bandit_expected_reward_eq_arm_occupation {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    ∫ h, (∑ t, (h t).2) ∂(banditMeasure ν π n) =
      ∑ i, banditArmMean ν i *
        ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n) := by
  sorry

end BanditAlgorithm
