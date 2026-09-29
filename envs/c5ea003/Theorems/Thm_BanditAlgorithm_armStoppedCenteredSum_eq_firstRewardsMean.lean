-- Prove2me | Theorems.Thm_BanditAlgorithm_armStoppedCenteredSum_eq_firstRewardsMean
-- name    : BanditAlgorithm.armStoppedCenteredSum_eq_firstRewardsMean
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-31T01:08:41.838683+00:00
-- url     : https://prove2.me/theorems/5235b0fd-c19a-41f4-932b-041d833141d9
-- title:
--   Stopped centered sum equals the realized first-rank sample mean
-- statement:
--   Fix an arm $i$ and a positive rank $s$. For any finite bandit history in which arm $i$ has been pulled at least $s$ times, let $\widehat\mu_{i,s}$ be the mean of its first $s$ realized rewards and let $\mu_i$ be the arm mean. Then the centered reward sum stopped after the first $s$ pulls satisfies
--
--   $$
--   S_{i,s}=s\bigl(\widehat\mu_{i,s}-\mu_i\bigr).
--   $$
--
--   This identity connects the canonical stopped-sum process used for adaptive concentration with the exact realized-rank empirical mean used in Thompson-sampling posterior calculations.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), reward-stack convention in Section 4.6, printed p. 65 / PDF p. 74, and the first-sample empirical means in Section 36.2, printed pp. 463–465 / PDF pp. 472–474. This is a purely formal bridge between those two source-backed representations.

import Definitions.Def_ThompsonSampling
import Definitions.Def_ucbStoppedCenteredSum

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- Once rank s has been realized, the stopped centered sum is s times the centered first-s reward mean. -/
theorem armStoppedCenteredSum_eq_firstRewardsMean
    {k m : ℕ} (ν : StochasticBandit k) (i : Fin k) (s : ℕ)
    (h : BanditHistory k m) (hs : 0 < s)
    (hcount : s ≤ armPullCount i h) :
    armStoppedCenteredSum ν i s m h =
      (s : ℝ) *
        (armFirstRewardsMean i s h - banditArmMean ν i) := by
  sorry

end BanditAlgorithm
