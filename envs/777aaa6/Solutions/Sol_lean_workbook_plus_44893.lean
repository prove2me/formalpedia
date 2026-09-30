-- Prove2me | solution 1 for lean_workbook_plus_44893
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:47:19.870687+00:00
-- url     : https://prove2.me/submissions/ed9bc76e-f9ff-4982-882a-4062f7262d2a

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 ^ 65 + 1 ≡ 0 [ZMOD 3] := by
  decide
