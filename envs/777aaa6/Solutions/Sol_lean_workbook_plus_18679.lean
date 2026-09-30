-- Prove2me | solution 1 for lean_workbook_plus_18679
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:23.027476+00:00
-- url     : https://prove2.me/submissions/c70de75f-6f79-4a96-a79f-bb58e179e3e1

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution :
  (2^2010 + 5^2011) % 3 = 0 := by
  omega
