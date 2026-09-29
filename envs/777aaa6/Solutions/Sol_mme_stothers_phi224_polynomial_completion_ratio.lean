-- Prove2me | solution 1 for mme_stothers_phi224_polynomial_completion_ratio
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:41:22.174174+00:00
-- url     : https://prove2.me/submissions/8a436615-a910-4c46-a4c5-df97f23fc871

import Definitions.Def_mme_stothers_phi224_profile_data
import Theorems.Thm_mme_stothers_phi224_marginal_profile_entropy_upper
import Theorems.Thm_mme_stothers_phi224_exact_profile_entropy_polynomial_lower

set_option autoImplicit false

theorem solution
    (N alpha beta gamma delta : ℕ) (hN : 0 < N)
    (hsum : alpha + 2 * beta + gamma + delta = N) :
    (Nat.card
        (MME.StothersFourth.Phi224.MarginalProfileWord
          N alpha beta gamma delta) : ℝ) ≤
      ((((2 * N + 1 : ℕ) : ℝ)) ^ 9 *
        (6 * (((2 * N + 1 : ℕ) : ℝ))) ^ 9) *
        (Nat.card
          (MME.StothersFourth.Phi224.ExactProfileWord
            N alpha beta gamma delta) : ℝ) := by
  have hu := mme_stothers_phi224_marginal_profile_entropy_upper N alpha beta gamma delta hN
  have hl := mme_stothers_phi224_exact_profile_entropy_polynomial_lower N alpha beta gamma delta hN hsum
  have ha : 0 ≤ (((2 * N + 1 : ℕ) : ℝ)) ^ 9 := by positivity
  exact hu.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hl ha)
