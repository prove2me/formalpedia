-- Prove2me | Theorems.Thm_lean_workbook_plus_37501
-- name    : lean_workbook_plus_37501
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/fb98fbb5-ed89-4402-a181-e8344d45b3ca
-- statement:
--   Prove that $\frac1{15} < \frac12\cdot\frac34\cdots\frac{99}{100} < \frac1{10}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37501 : (1 / 15 : ℝ) < ∏ i in Finset.Icc (1 : ℕ) 99, (i + 1) / (i + 2) ∧ ∏ i in Finset.Icc (1 : ℕ) 99, (i + 1) / (i + 2) < 1 / 10   :=  by sorry
