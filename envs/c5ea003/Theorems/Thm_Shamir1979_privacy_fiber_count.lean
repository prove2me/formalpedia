-- Prove2me | Theorems.Thm_Shamir1979_privacy_fiber_count
-- name    : Shamir1979.privacy_fiber_count
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-29T07:51:19.959116+00:00
-- url     : https://prove2.me/theorems/5bdd25a4-fd8f-40b4-a4e6-20074cfa3a94
-- title:
--   Section 2 — exact count of compatible random choices
-- statement:
--   For prime $p$ and $1\le k\le n<p$, fix a coalition $\Gamma$ with fewer than $k$ participants, any secret $s$, and any assignment of values to all their shares. Exactly $p^{k-1-|\Gamma|}$ coefficient vectors produce that assignment. The count is uniform over the secret and over the joint observation. When $|\Gamma|=k-1$, the number is one, matching the paper's unique-polynomial argument; the formula also covers smaller and empty coalitions.
-- source:
--   Adi Shamir, How to Share a Secret, Communications of the ACM 22(11), 612–613 (1979), https://doi.org/10.1145/359168.359176, §2, p. 613, the unique-extension and equally-likely-polynomials argument

import Definitions.Def_Shamir1979_Model

open scoped BigOperators
universe u

namespace Shamir1979

theorem privacy_fiber_count (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p)
    (Γ : Finset (Fin n)) (hΓ : Γ.card < k)
    (secret : ZMod p) (values : Observation p Γ) :
    fiberCount (k := k) Γ secret values = p ^ (k-1-Γ.card) := by sorry

end Shamir1979
