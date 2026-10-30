-- Prove2me | Theorems.Thm_Shamir1979_extension_consistency
-- name    : Shamir1979.extension_consistency
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-29T07:52:06.947578+00:00
-- url     : https://prove2.me/theorems/4c52b9fa-70f2-47a0-abab-27344694b854
-- title:
--   Section 2, property (2) — adding participants preserves existing shares
-- statement:
--   Keep the prime field, threshold, secret, and sharing polynomial fixed. Enlarging the participant set from $n$ to $m$, where $k\le n\le m<p$, leaves every existing participant's share unchanged. The comparison uses the same numerical identifier for that participant in the enlarged index type. Removing participants is the reverse restriction of this identity; the claim does not assert erasure of copies that a former participant retained.
-- source:
--   Adi Shamir, How to Share a Secret, Communications of the ACM 22(11), 612–613 (1979), https://doi.org/10.1145/359168.359176, §2, p. 613, useful property (2)

import Definitions.Def_Shamir1979_Model

open scoped BigOperators
universe u

namespace Shamir1979

theorem extension_consistency (p n m k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnm : n ≤ m) (hmp : m < p)
    (secret : ZMod p) (coins : Coins p k) (i : Fin n) :
    share (n := m) secret coins (i.castLE hnm) = share (n := n) secret coins i := by sorry

end Shamir1979
