-- Prove2me | solution 1 for lean_workbook_plus_19984
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:42:35.02546+00:00
-- url     : https://prove2.me/submissions/331c642b-8e37-4d8f-9084-d6e06d86553a

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  Nat.gcd 6994 5993 = 13 := by
  simp
