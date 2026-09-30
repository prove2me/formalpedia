-- Prove2me | solution 1 for lean_workbook_plus_58588
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T02:10:11.483285+00:00
-- url     : https://prove2.me/submissions/bb09b258-b29b-4160-9d6a-6851174ed0a7

import Mathlib.Analysis.Complex.Basic

theorem solution (s : Finset ℝ) (hs : s.card ≥ 13) :
    ∃ x y, x ∈ s ∧ y ∈ s ∧ (abs (x - y) ≤ (2 - Real.sqrt 2) * abs (1 + x * y)) := by
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨x, hx⟩ := hne
  refine ⟨x, x, hx, hx, ?_⟩
  rw [sub_self, abs_zero]
  apply mul_nonneg
  · nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  · exact abs_nonneg _
