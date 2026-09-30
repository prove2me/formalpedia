-- Prove2me | solution 1 for lean_workbook_plus_77493
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:21:47.435567+00:00
-- url     : https://prove2.me/submissions/b7276731-4782-486f-baa4-d4648cef5e9d

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution : ∀ m n p : ℝ, (m+n+p)^2 ≥ 3*(m*n+n*p+m*p) := by
  intro m n p
  nlinarith [sq_nonneg (m-n), sq_nonneg (n-p), sq_nonneg (p-m)]
