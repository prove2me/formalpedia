-- Prove2me | Definitions.Def_asymptoticUcbFailureCount
-- name    : asymptoticUcbFailureCount
-- status  : Definition
-- author  : @Harry_Xu
-- created : 2026-07-26T02:05:50.297894+00:00
-- url     : https://prove2.me/theorems/69772bf0-e19a-4a45-a06f-43d9c8faff08
-- title:
--   The two UCB failure counts in Eq. (8.4)
-- statement:
--   Fix a stochastic bandit $\nu$, an optimal arm $a$, a target arm $i$, a tolerance $\varepsilon$, and a length-$n$ history. After all arms are initialized, let $U_n$ count rounds where the optimal-arm UCB is at most $\mu^*-\varepsilon$, and let $V_n$ count rounds where arm $i$ is selected while its UCB is at least $\mu^*-\varepsilon$. asymptoticUcbFailureCount returns $(U_n,V_n)$, the two counts in Eq. (8.4).
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (CUP 2020), proof of Theorem 8.1, Eq. (8.4), printed pp. 119–120 / PDF pp. 128–129.

import Definitions.Def_asymptoticUcbPolicy
import Definitions.Def_banditHistoryPrefix

/-!
Lattimore--Szepesvári, *Bandit Algorithms* (CUP 2020), Theorem 8.1,
Eq. (8.4), printed pp. 119--120 / PDF pp. 128--129.

For a fixed optimal arm `a` and suboptimal arm `i`, Eq. (8.4) splits pulls
of `i` after initialization into two bad-index counts: underestimation of the
optimal arm and selection of `i` while its index crosses `μ* - ε`.
The explicit all-arms-initialized condition records the initialization branch
of `IsAsymptoticUCBPolicy`; it only restricts the two source counts.
-/

namespace BanditAlgorithm

/-- The pair of bad-index counts used in Eq. (8.4): optimal-arm
underestimation and selected-suboptimal-arm overshoot. -/
noncomputable def asymptoticUcbFailureCount {k n : ℕ}
    (ν : StochasticBandit k) (a i : Fin k) (ε : ℝ)
    (h : BanditHistory k n) : ℝ × ℝ :=
  let initialized := fun r : Fin n ↦
    ∀ j, armPullCount j (banditHistoryPrefixAt h r) ≠ 0
  let lowOptimal := ∑ r : Fin n,
    if initialized r ∧
        asymptoticUcbIndex a (banditHistoryPrefixAt h r) ≤
          banditOptimalMean ν - ε then (1 : ℝ) else 0
  let highSelected := ∑ r : Fin n,
    if initialized r ∧
        banditOptimalMean ν - ε ≤
          asymptoticUcbIndex i (banditHistoryPrefixAt h r) ∧
        (h r).1 = i then (1 : ℝ) else 0
  (lowOptimal, highSelected)

end BanditAlgorithm


