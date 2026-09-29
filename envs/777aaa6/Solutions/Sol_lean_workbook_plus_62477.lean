-- Prove2me | solution 1 for lean_workbook_plus_62477
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:18:33.61168+00:00
-- url     : https://prove2.me/submissions/5724843f-8178-4bb9-8070-6a292471fff7

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {g c : ℝ} (h : 4 * g ^ 2 - 4 * c < 0) : g ^ 2 < c := by
  (intros; simp_all)
