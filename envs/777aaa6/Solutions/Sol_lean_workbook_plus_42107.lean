-- Prove2me | solution 1 for lean_workbook_plus_42107
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:29:31.677911+00:00
-- url     : https://prove2.me/submissions/038886dd-ef6b-4f30-94f0-254eab3ff17d

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ)
  (f : ℝ → ℝ)
  (h : ℝ → ℝ)
  (h_def : ∀ x, h x = f x - f (a + x))
  (h0 : h 0 = f 0 - f a)
  (h1a : h (1 - a) = f (1 - a) - f 1) :
  h 0 * h (1 - a) = (f 0 - f a) * (f (1 - a) - f 1) := by
  (intros; simp_all)
