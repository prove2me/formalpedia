-- Prove2me | Theorems.Thm_Shamir1979_perfect_privacy
-- name    : Shamir1979.perfect_privacy
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-29T07:51:46.696171+00:00
-- url     : https://prove2.me/theorems/5bf44677-71a6-4fca-a912-3816fcfbf144
-- title:
--   Section 2 — perfect privacy of the joint share distribution
-- statement:
--   For prime $p$ and $1\le k\le n<p$, sample all $k-1$ nonconstant coefficients independently and uniformly from $\mathbb F_p$. For every fixed secret, every coalition $\Gamma$ of fewer than $k$ participants, and every joint assignment $y$ to their shares, the probability of observing $y$ is exactly $p^{-|\Gamma|}$. Probability is represented as the cardinality of the corresponding event divided by the cardinality of the finite sample space. This is joint privacy, rather than merely a claim about individual shares or the existence of alternative secrets.
-- source:
--   Adi Shamir, How to Share a Secret, Communications of the ACM 22(11), 612–613 (1979), https://doi.org/10.1145/359168.359176, §1, p. 612, condition (2), and §2, p. 613, privacy paragraph

import Definitions.Def_Shamir1979_Model

open scoped BigOperators
universe u

namespace Shamir1979

theorem perfect_privacy (p n k : Nat) [Fact (Nat.Prime p)]
    (hk : 0 < k) (hkn : k ≤ n) (hnp : n < p)
    (Γ : Finset (Fin n)) (hΓ : Γ.card < k)
    (secret : ZMod p) (values : Observation p Γ) :
    observationProbability (k := k) Γ secret values = (1 : Rat) / (p : Rat) ^ Γ.card := by sorry

end Shamir1979
