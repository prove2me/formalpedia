-- Prove2me | Theorems.Thm_lean_workbook_plus_18991
-- name    : lean_workbook_plus_18991
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/92104e85-74ed-41d7-a973-2ef119935fed
-- statement:
--   Prove that $\cos^2(a)=\frac{1+\cos(2a)}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18991 : ∀ a : ℝ, (cos a) ^ 2 = (1 + cos (2 * a)) / 2   :=  by sorry
