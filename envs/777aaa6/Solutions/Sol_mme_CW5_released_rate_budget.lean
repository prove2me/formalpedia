-- Prove2me | solution 1 for mme_CW5_released_rate_budget
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T15:13:18.648714+00:00
-- url     : https://prove2.me/submissions/04ecca53-f238-4880-a68c-09bfaf0c12e6

import Theorems.Thm_mme_CW5_base_log_bounds

/-- The released target totals leave a positive CW-five surplus after the
stated loss allowance. Matching these totals to actual extraction rates is
required separately. -/
theorem solution
    (outer parent child loss : ℝ)
    (ho : (6707994429 / 125000000 : ℝ) ≤ outer)
    (hp : (6627490041 / 250000000 : ℝ) ≤ parent)
    (hc : (200037213610 / 1000000000 : ℝ) ≤ child)
    (hl : loss ≤ (1 / 20000 : ℝ)) :
    144 * Real.log 7 < outer + parent + child - loss := by
  have hlog := (mme_CW5_base_log_bounds 2).2
  change Real.log ((7 : ℚ) : ℝ) ≤
    ((1945910149056 / 1000000000000 : ℚ) : ℝ) at hlog
  norm_num at hlog
  linarith


#print axioms solution
