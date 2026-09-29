-- Prove2me | solution 1 for lean_workbook_plus_74487
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:09:54.925669+00:00
-- url     : https://prove2.me/submissions/986ea325-7825-4850-beb6-5a2bccd65bac

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (ha : a - a^3 + a^5 >= 3) : a^6 >= 5 := by
  have hp := mul_nonneg (sq_nonneg (a-1)) (sq_nonneg (a^2-1/2))
  nlinarith only [ha,hp,sq_nonneg (a-1)]
