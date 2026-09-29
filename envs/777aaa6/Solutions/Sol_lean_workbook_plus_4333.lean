-- Prove2me | solution 1 for lean_workbook_plus_4333
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:31:36.489416+00:00
-- url     : https://prove2.me/submissions/bde07070-ae84-4230-ba02-ce32498a4e69

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution : 2 ^ 8731 ≡ 0 [ZMOD 8] := by
  apply Int.modEq_zero_iff_dvd.mpr
  exact (show (8 : ℤ) ∣ 2^3 by norm_num).trans (pow_dvd_pow 2 (by norm_num : 3 ≤ 8731))
