-- Prove2me | solution 1 for lean_workbook_plus_25238
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:56.998694+00:00
-- url     : https://prove2.me/submissions/9e208370-dc82-4c2c-ba9d-819b93734d8e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℝ → ℝ) (hf: f = fun x ↦ 0) : (∀ x y, (f (x * f y + y^3) = y * f x + f y ^3)) := by
  (intros; simp_all)
