-- Prove2me | Theorems.Thm_BanditAlgorithm_bayesian_ts_round_regret_sq_le_mutualInformation_increment
-- name    : BanditAlgorithm.bayesian_ts_round_regret_sq_le_mutualInformation_increment
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-01T23:45:26.887269+00:00
-- url     : https://prove2.me/theorems/b5ba5206-b861-4a71-9f5d-63f3db190c97
-- title:
--   One-round Thompson-sampling information-ratio bound
-- statement:
--   Let
--
--   $$
--   \Delta_t=\mathbb E\!\left[X_{t,A^*}-X_{t,A_t}\right]
--   $$
--
--   be the one-round Bayesian regret of posterior-sampling Thompson sampling, and let $I_t=I(H_t;A^*)$ be the mutual information between the history before round $t$ and the optimal action. If rewards lie in $[0,1]$, then
--
--   $$
--   \Delta_t^2\le \frac{k}{2}\bigl(I_{t+1}-I_t\bigr).
--   $$
--
--   This is the one-step information-ratio estimate: the squared expected regret is controlled by the information about $A^*$ revealed by the next action–reward observation.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge UP, 2020), https://tor-lattimore.com/downloads/book/book.pdf, printed pp. 470–471 (PDF pp. 479–480), Lemma 36.7 and the Bayes-rule equality at the end of its proof.

import Definitions.Def_BayesianHistoryMutualInformation

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.bayesian_ts_round_regret_sq_le_mutualInformation_increment
    {k n : ℕ} [NeZero k]
    (Q : Measure (Fin n → Fin k → ℝ)) [IsProbabilityMeasure Q]
    (hQ : ∀ᵐ X ∂Q, ∀ (s : Fin n) (a : Fin k), X s a ∈ Set.Icc (0 : ℝ) 1)
    {pi : BanditPolicy k} (hpi : IsBayesianTSPolicy Q pi) (t : Fin n) :
    (∫ p, (p.1 t (bayesianOptimalAction p.1) - p.1 t ((p.2 t).1))
      ∂bayesianAdversarialMeasure Q pi n le_rfl) ^ 2 ≤
      ((k : ℝ) / 2) *
        (bayesianHistoryMutualInformation Q pi (t.1 + 1) (Nat.succ_le_iff.mpr t.2) -
          bayesianHistoryMutualInformation Q pi t.1 (Nat.le_of_lt t.2)) := by
  sorry
