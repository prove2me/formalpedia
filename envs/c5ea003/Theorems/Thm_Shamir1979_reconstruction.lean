-- Prove2me | Theorems.Thm_Shamir1979_reconstruction
-- name    : Shamir1979.reconstruction
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-29T07:51:04.461736+00:00
-- url     : https://prove2.me/theorems/b6105439-d213-43a0-ab15-d616e93616cf
-- title:
--   Section 2 — reconstruction from any authorized coalition
-- statement:
--   Let $p$ be prime and $1\le k\le n<p$. Participants have the distinct public identifiers $1,\ldots,n$ in $\mathbb F_p$. For every secret, every coefficient vector, and every set $\Gamma$ of at least $k$ participants, the explicitly defined Lagrange-at-zero reconstruction formula returns the secret from their jointly observed shares. The formula uses all the supplied locations, so the statement covers coalitions larger than $k$ as well as those of size exactly $k$.
-- source:
--   Adi Shamir, How to Share a Secret, Communications of the ACM 22(11), 612–613 (1979), https://doi.org/10.1145/359168.359176, §2, p. 613, reconstruction paragraph

import Definitions.Def_Shamir1979_Model

open scoped BigOperators
universe u

namespace Shamir1979

theorem reconstruction (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p)
    (secret : ZMod p) (coins : Coins p k) (Γ : Finset (Fin n)) (hΓ : k ≤ Γ.card) :
    recover Γ (observe Γ secret coins) = secret := by sorry

end Shamir1979
