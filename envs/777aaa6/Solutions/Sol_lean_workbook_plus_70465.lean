-- Prove2me | solution 1 for lean_workbook_plus_70465
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:49:55.305747+00:00
-- url     : https://prove2.me/submissions/1ae1e326-ae40-4796-a86c-02c7a057a033

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 7 ^ 100 ≡ 1 [ZMOD 100] := by
  decide
