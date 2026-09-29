-- Prove2me | solution 1 for lean_workbook_plus_45580
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:04:46.825875+00:00
-- url     : https://prove2.me/submissions/854d92b9-2ed9-4e72-8def-0e1ed6a3955f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (a b c d e f : ℝ) : (a + d) ^ 2 + (b + e) ^ 2 + (c + f) ^ 2 ≥ (a + d) * (b + e) + (b + e) * (c + f) + (c + f) * (a + d) := by
  nlinarith [sq_nonneg ((a+d)-(b+e)), sq_nonneg ((b+e)-(c+f)), sq_nonneg ((c+f)-(a+d))]
