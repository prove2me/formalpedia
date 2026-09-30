-- Prove2me | solution 1 for lean_workbook_plus_38417
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:28.24703+00:00
-- url     : https://prove2.me/submissions/b8da4640-36e9-48c9-84cc-caeb4166d65b

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (444 * 418) % 703 = 0 := by
  norm_num
