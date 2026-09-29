-- Prove2me | solution 1 for lean_workbook_plus_28273
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:05:47.727208+00:00
-- url     : https://prove2.me/submissions/efa32ed9-e38d-49f6-977d-cb8d296f1126

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (g z: ℝ) (h : g + z ≤ 10^6) : g + z ≤ 10^6 := by
  (intros; simp_all)
