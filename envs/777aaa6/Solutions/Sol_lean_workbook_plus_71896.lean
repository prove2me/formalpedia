-- Prove2me | solution 1 for lean_workbook_plus_71896
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-04T23:03:51.069304+00:00
-- url     : https://prove2.me/submissions/0f618bb8-fe28-4ec9-95cd-14b2459de1bd

import Mathlib.Analysis.Complex.Basic

set_option maxHeartbeats 400000 in
theorem solution (x : ℝ) : (x - 1 / 2) ^ 2 ≥ 0 := by
  positivity
