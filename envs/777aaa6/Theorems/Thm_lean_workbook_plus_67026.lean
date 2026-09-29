-- Prove2me | Theorems.Thm_lean_workbook_plus_67026
-- name    : lean_workbook_plus_67026
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0e93b0f4-d877-49fc-bf0a-e95c6fe57c5d
-- statement:
--   If $a,b,c$ are real numbers, then $(c) \ \ \ a^2(b-c)^4+b^2(c-a)^4+c^2(a-b)^4\ge \frac 1{2}(a-b)^2(b-c)^2(c-a)^2.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67026 (a b c : ℝ) :
  a^2 * (b - c)^4 + b^2 * (c - a)^4 + c^2 * (a - b)^4 ≥
  1 / 2 * (a - b)^2 * (b - c)^2 * (c - a)^2   :=  by sorry
