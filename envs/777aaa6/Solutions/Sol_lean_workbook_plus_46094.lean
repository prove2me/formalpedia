-- Prove2me | solution 1 for lean_workbook_plus_46094
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:38:15.169414+00:00
-- url     : https://prove2.me/submissions/2aed2d38-08b2-4dba-964b-5120ed6f43df

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : Fin 7 → ℝ) (h : ∀ i j, i ≠ j → 1 < |a i - a j| + |b i - b j|) : 1 < |a 0 - a 1| + |b 0 - b 1| ∧ 1 < |a 1 - a 2| + |b 1 - b 2| ∧ 1 < |a 2 - a 3| + |b 2 - b 3| ∧ 1 < |a 3 - a 4| + |b 3 - b 4| ∧ 1 < |a 4 - a 5| + |b 4 - b 5| ∧ 1 < |a 5 - a 6| + |b 5 - b 6| ∧ 1 < |a 6 - a 7| + |b 6 - b 7| := by
  (intros; simp_all)
