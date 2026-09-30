-- Prove2me | solution 1 for lean_workbook_plus_15036
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:19:17.533268+00:00
-- url     : https://prove2.me/submissions/c8a06763-8dc5-4a18-a0dc-e9d180e64e73

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  Nat.lcm 4 6 = 12 := by
  decide
