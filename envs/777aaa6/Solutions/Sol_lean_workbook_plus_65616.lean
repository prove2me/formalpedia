-- Prove2me | solution 1 for lean_workbook_plus_65616
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:40.444798+00:00
-- url     : https://prove2.me/submissions/0b75a944-d937-487a-bab6-e506354c30df

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 7 ^ 25 ≡ 16 ^ 5 [MOD 29] := by
  decide
