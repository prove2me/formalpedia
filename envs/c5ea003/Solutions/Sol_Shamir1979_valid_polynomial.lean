-- Prove2me | solution 1 for Shamir1979.valid_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T09:04:07.830604+00:00
-- url     : https://prove2.me/submissions/d3fe81f8-2545-4609-accb-423d2ca6796a

import Mathlib
import Definitions.Def_Cryptography_ShamirSecretSharing
import Definitions.Def_Shamir1979_Model
open scoped BigOperators
universe u
open Shamir1979

theorem solution (p k : Nat) [Fact (Nat.Prime p)] (hk : 0 < k)
    (secret : ZMod p) (coins : Coins p k) :
    ShamirSecretSharing.ValidPolynomial k secret (sharingPolynomial secret coins) := by
  constructor
  · unfold sharingPolynomial
    have hk' : (k : WithBot ℕ) = ((k - 1 + 1 : ℕ) : WithBot ℕ) := by congr 1; omega
    rw [hk']
    refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
    · exact lt_of_le_of_lt Polynomial.degree_C_le (by exact_mod_cast Nat.succ_pos _)
    · refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
      rw [Finset.sup_lt_iff (by exact WithBot.bot_lt_coe _)]
      intro j _
      refine lt_of_le_of_lt (Polynomial.degree_monomial_le _ _) ?_
      exact_mod_cast (by omega : j.val + 1 < k - 1 + 1)
  · unfold sharingPolynomial
    simp [Polynomial.eval_finsetSum]
