-- Prove2me | solution 1 for lean_workbook_plus_60075
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:09.968522+00:00
-- url     : https://prove2.me/submissions/d97bf4c5-823b-4c97-9e1c-2ee5bb9e79e1

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2005 ≡ 0 [ZMOD 2005] := by
  norm_num
