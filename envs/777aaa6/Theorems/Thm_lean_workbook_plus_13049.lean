-- Prove2me | Theorems.Thm_lean_workbook_plus_13049
-- name    : lean_workbook_plus_13049
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/f0931318-a031-4bf2-89e7-fa4463bd2e54
-- statement:
--   $ \frac{1}{b^2}+\frac{1}{c^2}\ge\frac{2}{bc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13049 : ∀ b c : ℝ, (b * c ≠ 0 → 1 / b ^ 2 + 1 / c ^ 2 ≥ 2 / (b * c))   :=  by sorry
