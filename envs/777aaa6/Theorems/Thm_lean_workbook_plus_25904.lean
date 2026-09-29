-- Prove2me | Theorems.Thm_lean_workbook_plus_25904
-- name    : lean_workbook_plus_25904
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e3c0b972-453a-4992-b2e7-cf7ff946f29e
-- statement:
--   From $ \cos A = -\cos\frac{B+C}{2}$ follows $ \cos^{2}A = \cos^{2}\frac{B+C}{2}$ and $ 2\cos^{2}A = 2\cos^{2}\frac{B+C}{2}= \cos(B+C)+1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25904 :
  ∀ A B C : ℝ, A ∈ Set.Ioc 0 Real.pi ∧ B ∈ Set.Ioc 0 Real.pi ∧ C ∈ Set.Ioc 0 Real.pi →
    A + B + C = Real.pi → cos A = -cos ((B + C) / 2) → cos A ^ 2 = cos ((B + C) / 2) ^ 2 ∧ 2 * cos A ^ 2 = cos (B + C) + 1   :=  by sorry
