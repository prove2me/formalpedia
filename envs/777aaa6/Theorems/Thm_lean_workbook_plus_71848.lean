-- Prove2me | Theorems.Thm_lean_workbook_plus_71848
-- name    : lean_workbook_plus_71848
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c5bbfd8c-0d8a-4630-a0cd-06aec928dbe3
-- statement:
--   $2\sin x+6\cos x=2\sqrt{10}\to\frac{1}{\sqrt{10}}\sin x+\frac{3}{\sqrt{10}}\cos x=1\to (2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71848 (x : ℝ) (h : 2 * Real.sin x + 6 * Real.cos x = 2 * Real.sqrt 10) : 1 / Real.sqrt 10 * Real.sin x + 3 / Real.sqrt 10 * Real.cos x = 1   :=  by sorry
