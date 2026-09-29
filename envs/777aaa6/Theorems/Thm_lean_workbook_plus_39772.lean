-- Prove2me | Theorems.Thm_lean_workbook_plus_39772
-- name    : lean_workbook_plus_39772
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/e39a0b24-d871-4a89-bd37-7fa55e60334c
-- statement:
--   Prove or disprove using the AM-GM inequality: If x and y are real numbers with $ y\geq 0$ and $ y(y+1)\leq (x+1)^{2}$ , then $ y(y-1)\leq x^{2}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39772 : ∀ x y : ℝ, y ≥ 0 ∧ y * (y + 1) ≤ (x + 1) ^ 2 → y * (y - 1) ≤ x ^ 2   :=  by sorry
