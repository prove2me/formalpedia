-- Prove2me | solution 1 for lean_workbook_plus_32028
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:24.349917+00:00
-- url     : https://prove2.me/submissions/3d9849a5-af67-4e83-905d-19def313b418

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x + y + z = 3) : ∃ x y z : ℝ, (x + y + z = 3 ∧ (x * (x + y - z) ≤ 1 ∨ y * (y + z - x) ≤ 1 ∨ z * (z + x - y) ≤ 1)) :=
  ⟨1, 1, 1, by norm_num, Or.inl (by norm_num)⟩
