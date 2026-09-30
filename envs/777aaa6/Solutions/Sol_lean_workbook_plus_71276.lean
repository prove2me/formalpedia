-- Prove2me | solution 1 for lean_workbook_plus_71276
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:11.078587+00:00
-- url     : https://prove2.me/submissions/762fa514-4481-4869-bbf2-f4b51598a66d

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 10^81 ≡ 1 [ZMOD 729] := by
  decide
