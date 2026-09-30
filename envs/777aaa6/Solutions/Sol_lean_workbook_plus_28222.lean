-- Prove2me | solution 1 for lean_workbook_plus_28222
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T22:53:20.856492+00:00
-- url     : https://prove2.me/submissions/0fa9ac28-e595-46d2-9a57-46687af91e17

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution : 2 * 10 ^ 2009 < 11 ^ 2009 := by
  omega
