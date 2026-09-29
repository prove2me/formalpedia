-- Prove2me | Theorems.Thm_lean_workbook_plus_4593
-- name    : lean_workbook_plus_4593
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/449cd3c4-b98a-4831-8e09-2f39e9af6819
-- statement:
--   Prove that $\frac{2}{3}(a+b+c)^2 \ge a+b+c+ab+bc+ca$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4593 : ∀ a b c : ℝ, (2 / 3) * (a + b + c) ^ 2 ≥ a + b + c + a * b + b * c + c * a   :=  by sorry
