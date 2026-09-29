-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_asymptotic_ucb_finite_time_regret_bound
-- name    : BanditAlgorithm.bandit_asymptotic_ucb_finite_time_regret_bound
-- status  : Proved
-- author  : @ann
-- created : 2026-07-19T05:14:49.039687+00:00
-- url     : https://prove2.me/theorems/5b49ca82-a910-4104-a929-6d85b8ed8ee3
-- title:
--   Asymptotically optimal UCB finite-time regret bound
-- statement:
--   For an arbitrary 1-subgaussian finite-armed bandit and any instance of the asymptotically optimal UCB policy (Algorithm 6), choose separately for each suboptimal arm $i$ a number $0 < \varepsilon_i < \Delta_i$. Then the finite-horizon regret is at most
--
--   $$\sum_{i:\Delta_i>0} \Delta_i\left(1+\frac{5}{\varepsilon_i^2}+\frac{2}{(\Delta_i-\varepsilon_i)^2}\left(\log f(n)+\sqrt{\pi\log f(n)}+1\right)\right),$$
--
--   where $f(n)=1+n\log^2 n$. This is the armwise pre-infimum form of Eq. (8.1); taking the infimum independently over each admissible $\varepsilon_i$ gives the displayed theorem in the book. The statement includes all finite horizons and handles an empty set of suboptimal arms by the empty sum.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), Chapter 8, Theorem 8.1 and Eq. (8.1), printed pp. 117-120 / PDF pp. 126-129; proof decomposition Eq. (8.4) on printed p. 119 and the two expectation bounds through printed p. 120.

import Definitions.Def_banditRegret
import Definitions.Def_asymptoticUcbPolicy

open MeasureTheory ProbabilityTheory Filter

theorem BanditAlgorithm.bandit_asymptotic_ucb_finite_time_regret_bound {k : ℕ}
    {ν : StochasticBandit k} (hν : IsSubgaussianBandit 1 ν)
    {π : BanditPolicy k} (hπ : IsAsymptoticUCBPolicy π)
    (n : ℕ) (ε : Fin k → ℝ)
    (hε : ∀ i, 0 < banditGap ν i →
      0 < ε i ∧ ε i < banditGap ν i) :
    banditRegret ν π n ≤
      ∑ i ∈ Finset.univ.filter (fun i ↦ 0 < banditGap ν i),
        banditGap ν i *
          (1 + 5 / (ε i) ^ 2 +
            2 / (banditGap ν i - ε i) ^ 2 *
              (Real.log (asymptoticUcbSchedule n) +
                Real.sqrt (Real.pi * Real.log (asymptoticUcbSchedule n)) + 1)) := by
  sorry
