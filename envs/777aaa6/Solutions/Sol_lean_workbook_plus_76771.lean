-- Prove2me | solution 1 for lean_workbook_plus_76771
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:16:36.810041+00:00
-- url     : https://prove2.me/submissions/df2e8662-56a0-4a27-90a7-a3cd2d62654e

import Mathlib

theorem section_identity (a : ℝ) :
    12 * ((2 : ℝ)^2 - 2*1 + 1^2) * a^2 +
      3 * (4*2^3 + 5*2^2*1 - 9*2*1^2 + 4*1^3) * a +
      4*2^4 + 5*2^3*1 - 9*2*1^3 + 4*1^4 =
      36 * (a + 19/12)^2 - 1/4 := by ring

theorem solution : ¬ (∀ x y a : ℝ,
    12 * (x^2 - x*y + y^2) * a^2 +
      3 * (4*x^3 + 5*x^2*y - 9*x*y^2 + 4*y^3) * a +
      4*x^4 + 5*x^3*y - 9*x*y^3 + 4*y^4 ≥ 0) := by
  intro h
  have hbad := h 2 1 (-19/12)
  rw [section_identity] at hbad
  have heval : (36 : ℝ) * (-19/12 + 19/12)^2 - 1/4 = -(1/4) := by ring
  rw [heval] at hbad
  exact (not_le_of_gt (by norm_num : -(1/4 : ℝ) < 0)) hbad
