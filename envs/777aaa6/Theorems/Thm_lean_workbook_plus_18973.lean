-- Prove2me | Theorems.Thm_lean_workbook_plus_18973
-- name    : lean_workbook_plus_18973
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/106e1eae-9685-497a-ab36-07deca4d68a5
-- statement:
--   Case 2: $p^2-4q=(|p|-2)^2 \to q=|p|-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18973 (p q : ℤ) (h₁ : (p : ℝ)^2 - 4 * q = (abs p - 2)^2) : q = abs p - 1   :=  by sorry
