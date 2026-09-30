-- Prove2me | solution 1 for lean_workbook_plus_35666
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:37:51.101087+00:00
-- url     : https://prove2.me/submissions/608196c0-8265-480f-b251-4ecefdd8e602

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (50^100) > (100^50) := by
  norm_num
