-- Prove2me | Theorems.Thm_Shamir1979_valid_polynomial
-- name    : Shamir1979.valid_polynomial
-- status  : Proved
-- author  : @Victorized
-- created : 2026-10-29T07:50:38.654408+00:00
-- url     : https://prove2.me/theorems/0046f858-8a13-4768-91cb-b2aac1658cb1
-- title:
--   Section 2 — validity of the sharing polynomial
-- statement:
--   For a prime $p$ and positive threshold $k$, the polynomial built from a secret $s\in\mathbb F_p$ and an arbitrary vector of $k-1$ coefficients has degree strictly below $k$ and evaluates to $s$ at zero. Coefficients may be zero, including the leading coefficient. This connects the concrete coefficient-vector construction to the existing `ShamirSecretSharing.ValidPolynomial` interface, which means exactly these two algebraic conditions.
-- source:
--   Adi Shamir, How to Share a Secret, Communications of the ACM 22(11), 612–613 (1979), https://doi.org/10.1145/359168.359176, §2, p. 613, the displayed construction of q(x)

import Definitions.Def_Cryptography_ShamirSecretSharing
import Definitions.Def_Shamir1979_Model

open scoped BigOperators
universe u

namespace Shamir1979

theorem valid_polynomial (p k : Nat) [Fact (Nat.Prime p)] (hk : 0 < k)
    (secret : ZMod p) (coins : Coins p k) :
    ShamirSecretSharing.ValidPolynomial k secret (sharingPolynomial secret coins) := by sorry

end Shamir1979
