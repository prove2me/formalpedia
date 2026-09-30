-- Prove2me | solution 1 for lean_workbook_plus_27618
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:13:30.316606+00:00
-- url     : https://prove2.me/submissions/7703c5cc-5836-428a-98c9-66e32800ed3d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x n k : ℤ) (h₁ : x ≡ n [ZMOD 4]) : x ^ 2 ≡ n ^ 2 [ZMOD 8] := by
  rw [Int.modEq_iff_dvd] at h₁ ⊢
  obtain ⟨t, ht⟩ := h₁
  have hn : n = x + 4 * t := by omega
  rw [hn]
  refine ⟨x * t + 2 * t ^ 2, ?_⟩
  ring

#print axioms solution
