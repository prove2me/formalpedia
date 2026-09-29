-- Prove2me | solution 1 for lean_workbook_plus_64422
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T06:48:28.001197+00:00
-- url     : https://prove2.me/submissions/fddfc68c-5761-4a64-8794-2c7d75ba66ba

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (α : ℝ) (h : α = -(4 + Real.sqrt 10) / 3) : α = -(4 + Real.sqrt 10) / 3 := by
  (intros; simp_all)
