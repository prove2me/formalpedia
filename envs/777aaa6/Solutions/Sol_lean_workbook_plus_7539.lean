-- Prove2me | solution 1 for lean_workbook_plus_7539
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T03:28:19.179066+00:00
-- url     : https://prove2.me/submissions/75265404-d2b6-44e4-bc34-6e2225a7cb4a

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℤ) (h : x * y * z ≠ 0) : x^4 + 2*y^4 = z^2 ↔ ∃ x0 y0 z0 : ℤ, x0 * y0 * z0 ≠ 0 ∧ x^4 + 2*y^4 = z^2 := by
  constructor
  · intro hxyz
    exact ⟨1, 1, 1, by norm_num, hxyz⟩
  · rintro ⟨_, _, _, _, hxyz⟩
    exact hxyz
