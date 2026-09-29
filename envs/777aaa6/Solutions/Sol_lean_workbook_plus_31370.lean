-- Prove2me | solution 1 for lean_workbook_plus_31370
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:56:11.55115+00:00
-- url     : https://prove2.me/submissions/fcba7388-a3ce-4242-b758-19a101649618

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : 2008^2 + 2^2008 ≡ 0 [ZMOD 4] := by
  apply Int.modEq_zero_iff_dvd.mpr
  apply dvd_add
  · norm_num
  · exact (show (4:ℤ) ∣ 2^2 by norm_num).trans (pow_dvd_pow 2 (by omega : 2 ≤ 2008))
