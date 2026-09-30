-- Prove2me | solution 1 for lean_workbook_plus_125
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:34:32.223881+00:00
-- url     : https://prove2.me/submissions/00957976-f98a-4970-842e-e6c4b95620a1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

theorem solution (a b c d : ℤ)
    (h : ∀ x, 5 ∣ a * x ^ 3 + b * x ^ 2 + c * x + d) :
    5 ∣ a ∧ 5 ∣ b ∧ 5 ∣ c ∧ 5 ∣ d := by
  have h0 := h 0
  have h1 := h 1
  have hm1 := h (-1)
  have h2 := h 2
  norm_num at h0 h1 hm1 h2
  omega

#print axioms solution
