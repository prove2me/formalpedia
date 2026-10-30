-- Prove2me | Theorems.Thm_Shamir1979_threshold_scheme
-- name    : Shamir1979.threshold_scheme
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-29T07:53:24.966912+00:00
-- url     : https://prove2.me/theorems/20c6f3e9-0d1c-4d55-8dce-b5c2f14fec13
-- title:
--   Shamir’s threshold scheme: reconstruction and perfect privacy
-- statement:
--   For every prime $p$ and every threshold configuration $1\le k\le n<p$, the concrete polynomial scheme with participant identifiers $1,\ldots,n$ satisfies both defining requirements of a threshold scheme. Any coalition of at least $k$ participants reconstructs the secret by the given Lagrange formula, for every choice of random coefficients. Any coalition of fewer than $k$ participants has exactly the same uniform joint observation distribution for every fixed secret when the coefficients are sampled independently and uniformly. Thus reconstruction and perfect privacy are conclusions about the actual construction, not assumptions about an abstract scheme. The empty observation and the positive-threshold boundary $k=1$ are included.
-- source:
--   Adi Shamir, How to Share a Secret, Communications of the ACM 22(11), 612–613 (1979), https://doi.org/10.1145/359168.359176, §1, p. 612, conditions (1)–(2), and §2, p. 613, complete finite-field construction

import Definitions.Def_Shamir1979_Model

open scoped BigOperators
universe u

namespace Shamir1979

theorem threshold_scheme (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p) :
    (∀ (secret : ZMod p) (coins : Coins p k) (Γ : Finset (Fin n)),
      k ≤ Γ.card → recover Γ (observe Γ secret coins) = secret) ∧
    (∀ (secret : ZMod p) (Γ : Finset (Fin n)) (values : Observation p Γ),
      Γ.card < k → observationProbability (k := k) Γ secret values =
        (1 : Rat) / (p : Rat) ^ Γ.card) := by sorry

end Shamir1979
