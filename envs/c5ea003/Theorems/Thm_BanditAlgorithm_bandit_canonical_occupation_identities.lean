-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_canonical_occupation_identities
-- name    : BanditAlgorithm.bandit_canonical_occupation_identities
-- status  : Proved
-- author  : @MKPynnic
-- created : 2026-07-18T16:45:33.185337+00:00
-- url     : https://prove2.me/theorems/ca767502-076a-4efb-b949-d7fced59f74f
-- title:
--   Canonical bandit occupation identities
-- statement:
--   For the canonical finite-armed bandit model with integrable reward laws, the expected cumulative reward is the arm-mean-weighted expected occupation count,
--   $$\mathbb{E}\!\left[\sum_{t=1}^n X_t\right]=\sum_{i=1}^k \mu_i\,\mathbb{E}[T_i(n)],$$
--   and the expected occupation counts sum to the horizon, $\sum_i \mathbb E[T_i(n)]=n$. The first identity is the conditional-reward calculation in the proof of the regret decomposition lemma; the second is the finite indicator identity $\sum_i \mathbf 1\{A_t=i\}=1$ summed over rounds.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Lemma 4.5, printed p. 63, especially Eq. (4.6), https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_banditRegret

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem bandit_canonical_occupation_identities {k : ℕ} (ν : StochasticBandit k)
    (hInt : ∀ i, Integrable id (ν.P i)) (π : BanditPolicy k) (n : ℕ) :
    (∫ h, (∑ t, (h t).2) ∂(banditMeasure ν π n) =
      ∑ i, banditArmMean ν i *
        ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n)) ∧
    (∑ i, ∫ h, (armPullCount i h : ℝ) ∂(banditMeasure ν π n)) = n := by
  sorry

end BanditAlgorithm
