-- Prove2me | Theorems.Thm_lean_workbook_plus_71315
-- name    : lean_workbook_plus_71315
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/3dd5c9df-a5ca-445e-baaa-14741fe257f3
-- statement:
--   Simplify the expression \(\frac{\sin(x)}{\cos(x)} + \frac{\cos(x)}{\sin(x)}\) and show that it equals \(\frac{1}{\sin(x)\cos(x)}\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71315 (x : ℝ) (hx : sin x ≠ 0 ∧ cos x ≠ 0) : sin x / cos x + cos x / sin x = 1 / (sin x * cos x)   :=  by sorry
