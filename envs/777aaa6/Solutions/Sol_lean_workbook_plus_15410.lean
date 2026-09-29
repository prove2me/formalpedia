-- Prove2me | solution 1 for lean_workbook_plus_15410
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:18:11.016963+00:00
-- url     : https://prove2.me/submissions/8126d24f-d4a4-45f7-a20b-fd0a431389ca

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a : ℝ) (h : 2*a^6 - 2*a^4 + a^2 = 3/2) : a^8 > 1 := by
  have ht : 1<a^2 := by
    by_contra hn
    have hp := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (a^2)) (show a^2-1≤0 by linarith)
    nlinarith only [hp,h,show a^2≤1 by linarith]
  have hp := mul_pos (show 0<a^2-1 by linarith) (show 0<a^6+a^4+a^2+1 by positivity)
  nlinarith only [hp]
