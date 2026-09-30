-- Prove2me | solution 1 for lean_workbook_plus_44220
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:24:40.085031+00:00
-- url     : https://prove2.me/submissions/b29ead9e-f717-48d7-8fcf-a807d2531ed3

import Mathlib.Analysis.Complex.Basic

set_option exponentiation.threshold 3000 in
theorem solution : 1997 ∣ (1336 ^ 1997 + 1339 ^ 1997 - 1995 ^ 1997 - 1998 ^ 1997) := by
  norm_num
