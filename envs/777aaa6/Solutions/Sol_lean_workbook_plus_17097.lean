-- Prove2me | solution 1 for lean_workbook_plus_17097
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:57:27.0613+00:00
-- url     : https://prove2.me/submissions/18ada6d5-6feb-4bdc-9a89-178b054a5ba1

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : (4^250 ≡ 4^125 [ZMOD 12]) := by
  decide
