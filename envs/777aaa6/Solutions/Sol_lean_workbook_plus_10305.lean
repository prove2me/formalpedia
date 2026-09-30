-- Prove2me | solution 1 for lean_workbook_plus_10305
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:17:23.483571+00:00
-- url     : https://prove2.me/submissions/8be0aeac-7d07-49fd-9172-6cdb92144026

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℝ → ℝ) (hf: f = fun x ↦ x) : ∀ x y, f (x + y - f (x*y)) = f (1 - x) * f y + f x := by
  subst hf
  intro x y
  simp only
  ring
