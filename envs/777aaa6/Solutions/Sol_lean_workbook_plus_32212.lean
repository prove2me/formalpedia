-- Prove2me | solution 1 for lean_workbook_plus_32212
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:39:51.215577+00:00
-- url     : https://prove2.me/submissions/a6eff00b-ef06-434f-a42b-16a7163766b5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (f : ℤ → ℤ) (h : ∃ c, ∀ x, f x = c) : ∃ c, ∀ x, f x = c := by
  (intros; simp_all)
