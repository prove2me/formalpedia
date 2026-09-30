-- Prove2me | solution 1 for lean_workbook_plus_64582
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:06.8465+00:00
-- url     : https://prove2.me/submissions/bd6772ad-8b45-4003-9a7e-76a74ebcd259

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 13 ^ 0 ≡ 1 [ZMOD 10] := by
  norm_num
