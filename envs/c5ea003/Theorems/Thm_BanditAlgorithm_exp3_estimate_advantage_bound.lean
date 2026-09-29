-- Prove2me | Theorems.Thm_BanditAlgorithm_exp3_estimate_advantage_bound
-- name    : BanditAlgorithm.exp3_estimate_advantage_bound
-- status  : Proved
-- author  : @ann
-- created : 2026-07-18T17:15:41.645059+00:00
-- url     : https://prove2.me/theorems/5742c006-60b0-4c30-8e6b-698a447980bb
-- title:
--   Exp3 expected estimated-advantage bound
-- statement:
--   For every comparator arm $i$, the expected cumulative Exp3 estimate for $i$ minus the learner’s expected collected reward is at most $\log(k)/\eta+\eta n k/2$. This is the expectation form of the exponential-weights potential inequality (11.15), using that the total expected loss-estimator mass is at most $nk$.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), Theorem 11.2 proof, printed pp. 156–157, especially Eq. (11.15) and the expectation calculation immediately following it; Eq. (11.9) printed p. 153 identifies the expected estimated advantage. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

theorem exp3_estimate_advantage_bound
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (π : BanditPolicy k) (η : ℝ) (hη : 0 < η) (hπ : IsExp3Policy η π)
    (i : Fin k) :
    (∫ h, exp3Estimate η n h i ∂(adversarialMeasure x π n)) -
        (∫ h, (∑ t, (h t).2) ∂(adversarialMeasure x π n)) ≤
      Real.log k / η + η * n * k / 2 := by
  sorry
end BanditAlgorithm
