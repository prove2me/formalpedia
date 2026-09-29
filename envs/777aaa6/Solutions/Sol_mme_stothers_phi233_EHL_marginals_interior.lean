-- Prove2me | solution 1 for mme_stothers_phi233_EHL_marginals_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:50:22.311718+00:00
-- url     : https://prove2.me/submissions/1234ecd8-ae99-4aeb-8c32-fdb22f25be49

import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-- The Davie--Stothers ratios determined by `E,H,L` lie strictly inside the
`phi_233` marginal region whenever `E` and `H` are positive and smaller than
`L`. -/
theorem solution
    (E H L : ℝ) (hE : 0 < E) (hH : 0 < H)
    (hEL : E < L) (hHL : H < L) :
    let sigma := 2 * H / (2 * H + L)
    let mu := E / (E + L)
    0 < sigma ∧ 0 < mu ∧ sigma < 1 ∧ sigma / 2 + mu < 1 := by
  dsimp
  have hL : 0 < L := lt_trans hH hHL
  have hS : 0 < 2 * H + L := by positivity
  have hM : 0 < E + L := by positivity
  constructor
  · positivity
  constructor
  · positivity
  constructor
  · exact (div_lt_one hS).2 (by linarith)
  · have hid :
        (2 * H / (2 * H + L)) / 2 + E / (E + L) =
          (H * (E + L) + E * (2 * H + L)) /
            ((2 * H + L) * (E + L)) := by
      field_simp [ne_of_gt hS, ne_of_gt hM]
    rw [hid]
    apply (div_lt_one (mul_pos hS hM)).2
    have hEH : E * H < L * H := mul_lt_mul_of_pos_right hEL hH
    have hLL : 0 < L * L := mul_pos hL hL
    nlinarith
