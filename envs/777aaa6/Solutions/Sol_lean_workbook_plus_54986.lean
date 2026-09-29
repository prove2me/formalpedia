-- Prove2me | solution 1 for lean_workbook_plus_54986
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:30:20.116805+00:00
-- url     : https://prove2.me/submissions/1417f972-5675-4a59-952f-bbaf7dead327

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d e : ℝ) (ha : a = 1 / 5) (hb : b = 1 / 5) (hc : c = 1 / 5) (hd : d = 1 / 5) (he : e = 1 / 5) : a * b * c * d * e + 4 ≥ a * b * c * d + a * b * c * e + a * b * d * e + a * c * d * e + b * c * d * e := by
  rw [ha,hb,hc,hd,he]
  norm_num
