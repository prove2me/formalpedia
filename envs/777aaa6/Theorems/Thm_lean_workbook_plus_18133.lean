-- Prove2me | Theorems.Thm_lean_workbook_plus_18133
-- name    : lean_workbook_plus_18133
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/fa4c2302-d9e6-4867-b0d4-d28bfca1096e
-- statement:
--   Prove that $\left(\sum a^2\right)^2\geq \sum a^3c$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18133 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ a ^ 3 * c + b ^ 3 * a + c ^ 3 * b   :=  by sorry
