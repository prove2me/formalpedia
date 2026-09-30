-- Prove2me | solution 1 for lean_workbook_plus_8510
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:38:32.533208+00:00
-- url     : https://prove2.me/submissions/daff8ea2-2bab-483c-8ecc-b07d5cac2f71

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 10010 ≡ 35 [MOD 665] := by
  decide
