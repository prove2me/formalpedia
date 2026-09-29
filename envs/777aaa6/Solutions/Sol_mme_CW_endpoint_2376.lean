-- Prove2me | solution 1 for mme_CW_endpoint_2376
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-23T23:43:22.280469+00:00
-- url     : https://prove2.me/submissions/70d3bb6a-d95b-4d79-8921-edfaf77d34df

import Definitions.Def_mme_CW_auxiliary_RHS
import Theorems.Thm_mme_CW_auxiliary_mono
import Theorems.Thm_mme_CW_auxiliary_numeric_2376

open MME

theorem solution
    (w : ℝ)
    (haux :
      auxiliaryRHS 6 (w / 3) cw2376_a cw2376_b cw2376_c cw2376_d ≤ 64) :
    w < 297 / 125 := by
  have hnumeric :
      (64 : ℝ) <
        auxiliaryRHS 6 (99 / 125) cw2376_a cw2376_b cw2376_c cw2376_d := by
    rw [auxiliaryRHS, cw2376_a, cw2376_b, cw2376_c, cw2376_d]
    rw [show (2 : ℝ) * ((6 : ℕ) : ℝ) = 12 by norm_num,
      show (((6 : ℕ) : ℝ) ^ (2 : ℕ)) + 2 = 38 by norm_num,
      show (616627 : ℝ) / 3000000 = 616627 / (3 * 1000000) by norm_num]
    exact mme_CW_auxiliary_numeric_2376
  by_contra hw
  rw [not_lt] at hw
  have htau : (99 / 125 : ℝ) ≤ w / 3 := by linarith
  have hmono := mme_CW_auxiliary_mono (99 / 125) (w / 3) htau
  linarith
