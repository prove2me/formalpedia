-- Prove2me | solution 1 for lean_workbook_plus_67379
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:00:29.409165+00:00
-- url     : https://prove2.me/submissions/0858ee81-e244-4667-bcbe-07519e7c8615

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (a : ℤ) : a > 3 → a^3 > 12 * a := by
  intros; nlinarith [sq_nonneg (by assumption : _), sq_nonneg 1]
