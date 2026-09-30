-- Prove2me | solution 1 for lean_workbook_plus_59191
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:37:31.400349+00:00
-- url     : https://prove2.me/submissions/65654104-83f9-4346-b002-d8c4ba87e00e

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

theorem solution (f : ℕ → ℕ) :
    ¬ ∀ m n, (m + f n) ^ 2 ≥ 3 * (f m) ^ 2 + n ^ 2 := by
  intro h
  have hzero := h 0 0
  norm_num at hzero
  have hfzero : f 0 = 0 := by nlinarith
  have h01 := h 0 1
  have h10 := h 1 0
  rw [hfzero] at h01 h10
  norm_num at h01 h10
  omega

#print axioms solution
