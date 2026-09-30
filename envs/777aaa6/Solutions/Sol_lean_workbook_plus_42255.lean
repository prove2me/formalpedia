-- Prove2me | solution 1 for lean_workbook_plus_42255
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:38:26.226123+00:00
-- url     : https://prove2.me/submissions/f9e70c8b-b9a8-4c65-937c-7f0e2afc6e04

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum

theorem solution (f : ℝ → ℝ)
    (hf : ∀ x y, f (x + y) = f x * f y) (h : f 0 ≠ 0) :
    ∀ x, f (-x) = 1 / f x := by
  have hz : f 0 = 1 := by
    apply mul_left_cancel₀ h
    simpa using (hf 0 0).symm
  intro x
  have hp : f x * f (-x) = 1 := by
    simpa [hz] using (hf x (-x)).symm
  have hx : f x ≠ 0 := by
    intro hx
    rw [hx, zero_mul] at hp
    norm_num at hp
  apply (eq_div_iff hx).2
  simpa [mul_comm] using hp
