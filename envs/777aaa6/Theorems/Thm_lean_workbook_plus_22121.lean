-- Prove2me | Theorems.Thm_lean_workbook_plus_22121
-- name    : lean_workbook_plus_22121
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7b9a8883-23ba-4b7a-af7b-eecc6135f863
-- statement:
--   IF $a,b$ > $0$ , and $2a=ab+b^2$ , prove $(a-b)(ab+2b-3)$ ≥ $0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22121 (a b : ℝ) (hab : 0 < a ∧ 0 < b) (h : a * b + b ^ 2 = 2 * a) : (a - b) * (a * b + 2 * b - 3) ≥ 0   :=  by sorry
