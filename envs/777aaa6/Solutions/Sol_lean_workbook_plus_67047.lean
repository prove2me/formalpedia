-- Prove2me | solution 1 for lean_workbook_plus_67047
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:07:55.383223+00:00
-- url     : https://prove2.me/submissions/4c626f4c-e8ac-4271-a010-39aee0c89548

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (a₁ a₂ a₃ b₁ b₂ b₃ : ℝ) :
    (a₁^2 + a₂^2 + a₃^2) * (b₁^2 + b₂^2 + b₃^2) ≥
      a₁^2 * b₁^2 + a₂^2 * b₂^2 + a₃^2 * b₃^2 +
      2 * a₁ * b₂ * a₂ * b₁ + 2 * a₁ * b₃ * a₃ * b₁ + 2 * a₂ * b₃ * a₃ * b₂ := by
  nlinarith only [sq_nonneg (a₁*b₂-a₂*b₁), sq_nonneg (a₂*b₃-a₃*b₂),
    sq_nonneg (a₃*b₁-a₁*b₃)]

#print axioms solution
