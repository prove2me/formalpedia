-- Prove2me | solution 1 for lean_workbook_plus_55148
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:10:02.919801+00:00
-- url     : https://prove2.me/submissions/344067ef-2423-4ff0-90c4-61de6a4f1ed3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ ε : ℝ, 0 < ε ∧ ε < 1 →
    1 - ε + (1 / (1 - ε)) ≥ 1 + ε + (1 / (1 + ε)) := by
  rintro ε ⟨hε, hε1⟩
  have hm : 0 < 1 - ε := by linarith
  have hp : 0 < 1 + ε := by linarith
  have hid :
      (1 - ε + 1 / (1 - ε) - (1 + ε + 1 / (1 + ε))) * ((1 - ε) * (1 + ε)) =
        2 * ε ^ 3 := by
    field_simp [hm.ne', hp.ne']
    ring
  have hprod : 0 ≤
      (1 - ε + 1 / (1 - ε) - (1 + ε + 1 / (1 + ε))) * ((1 - ε) * (1 + ε)) := by
    rw [hid]
    positivity
  have hd := nonneg_of_mul_nonneg_left hprod (mul_pos hm hp)
  linarith

#print axioms solution
