-- Prove2me | solution 1 for lean_workbook_plus_41280
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:16.551426+00:00
-- url     : https://prove2.me/submissions/31b1c894-313e-4589-a918-fc04e78971d4

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2^36 ≡ 736 [MOD 1000] := by
  decide
