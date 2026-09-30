-- Prove2me | solution 2 for lean_workbook_plus_49747
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:35:44.565714+00:00
-- url     : https://prove2.me/submissions/b65f9e5d-d3d9-4600-aec3-e2193169791e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) (h₁ : a ≠ 24) (h₂ : b = 24 * (a - 12) / (a - 24)) : b = 24 * (a - 12) / (a - 24) := by
  (intros; simp_all)
