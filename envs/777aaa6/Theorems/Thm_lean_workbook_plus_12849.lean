-- Prove2me | Theorems.Thm_lean_workbook_plus_12849
-- name    : lean_workbook_plus_12849
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b2d9a5eb-cd06-460c-8771-bbf770e05e27
-- statement:
--   Prove that $\frac{x^2}{2} - (1 - cos x) < \frac{x^2}{24}$ , where $x > 0 $ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12849 : ∀ x > 0, (x^2 / 2 - (1 - Real.cos x)) < x^2 / 24   :=  by sorry
