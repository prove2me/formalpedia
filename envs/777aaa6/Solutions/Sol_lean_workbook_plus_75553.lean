-- Prove2me | solution 1 for lean_workbook_plus_75553
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:39:24.232594+00:00
-- url     : https://prove2.me/submissions/0a0bf370-33ac-4da4-bbce-8a81ab99fa20

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.LinearCombination

theorem solution (F : Type*) [Field F] (h : ¬∃ x : F, x^2 = -1)
    (x y : F) (hxy : x^2+y^2 = 0) : x = 0 ∧ y = 0 := by
  by_cases hy : y = 0
  · have hx : x^2 = 0 := by simpa [hy] using hxy
    exact ⟨pow_eq_zero hx, hy⟩
  · exfalso
    apply h
    refine ⟨x/y, ?_⟩
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 hy)).mpr
    linear_combination hxy
