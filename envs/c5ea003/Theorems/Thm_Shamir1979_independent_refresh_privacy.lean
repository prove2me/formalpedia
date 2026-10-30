-- Prove2me | Theorems.Thm_Shamir1979_independent_refresh_privacy
-- name    : Shamir1979.independent_refresh_privacy
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-29T07:52:32.469979+00:00
-- url     : https://prove2.me/theorems/5632a099-5496-42d7-95e3-bc922e05d890
-- title:
--   Section 2, property (3) — privacy across independent refreshes
-- statement:
--   For prime $p$ and $1\le k\le n<p$, take any finite collection of sharing editions. Every edition has the same secret constant and a freshly, independently, uniformly sampled vector of nonconstant coefficients. The observed coalition may differ between editions but must contain fewer than $k$ participants in each. Every specified combined transcript then has probability $p^{-\sum_e |\Gamma_e|}$, independent of the secret. The finite collection may be empty. Independent resampling is part of the sample space; correlated refresh randomness is not covered.
-- source:
--   Adi Shamir, How to Share a Secret, Communications of the ACM 22(11), 612–613 (1979), https://doi.org/10.1145/359168.359176, §2, p. 613, useful property (3), under the stated fresh-independent-polynomial sampling convention

import Definitions.Def_Shamir1979_Model

open scoped BigOperators
universe u

namespace Shamir1979

theorem independent_refresh_privacy (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p)
    {E : Type u} [Fintype E] (groups : E → Finset (Fin n))
    (hgroups : ∀ e, (groups e).card < k) (secret : ZMod p)
    (values : (e : E) → Observation p (groups e)) :
    epochProbability (k := k) groups secret values =
      (1 : Rat) / (p : Rat) ^ (∑ e : E, (groups e).card) := by sorry

end Shamir1979
