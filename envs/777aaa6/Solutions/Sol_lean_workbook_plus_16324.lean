-- Prove2me | solution 1 for lean_workbook_plus_16324
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:12:16.839349+00:00
-- url     : https://prove2.me/submissions/91e604d9-84a1-4893-af3c-1c003e5e5b1a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (h1 : 3 / 5 ≤ a) (h2 : a ≤ 4 / 5) : a ∈ Set.Icc (3 / 5) (4 / 5) := by
  (intros; simp_all)
