-- Prove2me | solution 1 for lean_workbook_plus_76916
-- status  : ACCEPTED   (disprove)
-- author  : @ryanshin
-- created : 2026-09-05T05:35:48.717743+00:00
-- url     : https://prove2.me/submissions/5764db98-a2b7-4366-bc50-460f0b58a418

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution : ¬ ({n : ℕ | 1 < n ∧ (n-1) ∣ 60} = {2,3,5,7,11,13,31,61}) := by
  intro h
  have hfour : 4 ∈ ({n : ℕ | 1 < n ∧ (n-1) ∣ 60} : Set ℕ) := by norm_num
  rw [h] at hfour
  norm_num at hfour
