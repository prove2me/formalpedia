-- Prove2me | solution 1 for lean_workbook_plus_71909
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:44:54.957339+00:00
-- url     : https://prove2.me/submissions/b3c87a2b-63ad-40d0-b96d-a3d833306bf1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution : ∀ a b c d : ℝ, a * b = 1 ∧ a * c + b * d = 2 → 1 - c * d ≥ 0 := by
  rintro a b c d ⟨hab, hsum⟩
  have hprod := congrArg (fun x : ℝ => x * (c * d)) hab
  nlinarith [sq_nonneg (a * c - b * d)]

#print axioms solution
