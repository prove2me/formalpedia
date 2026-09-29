-- Prove2me | Theorems.Thm_BanditAlgorithm_exp3_estimate_unbiased
-- name    : BanditAlgorithm.exp3_estimate_unbiased
-- status  : Proved
-- author  : @ann
-- created : 2026-07-18T17:15:19.748014+00:00
-- url     : https://prove2.me/theorems/aa41a552-2ba5-499b-8b0f-042cb16cc1f0
-- title:
--   Exp3 loss-based estimate is unbiased
-- statement:
--   For every arm $i$, the cumulative loss-based importance-weighted Exp3 reward estimate is unbiased: under the adversarial interconnection measure, its expectation equals the deterministic cumulative reward of arm $i$ through horizon $n$. The reward matrix lies in $[0,1]$, the learning rate is positive, and the policy is exactly Exp3.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), §11.2 Eq. (11.6) printed p. 151 and Theorem 11.1 proof Eq. (11.8) printed p. 153. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem exp3_estimate_unbiased
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hη : 0 < η) (hπ : IsExp3Policy η π)
    (i : Fin k) :
    (∫ h, exp3Estimate η n h i ∂(adversarialMeasure x π n)) =
      ∑ t : Fin n, x t i := by
  sorry
end BanditAlgorithm
