-- Prove2me | Theorems.Thm_lean_workbook_plus_33872
-- name    : lean_workbook_plus_33872
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/4eed8e61-5c16-4d62-a24b-d8bcfa05dc7a
-- statement:
--   Prove that $\sum_{cyc}(a-b)^4 + \sum_{cyc}ab(a-b)^2 \ge 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33872 (a b c : ℝ) :
  (a - b) ^ 4 + (b - c) ^ 4 + (c - a) ^ 4 + a * b * (a - b) ^ 2 + b * c * (b - c) ^ 2 + c * a * (c - a) ^ 2 ≥ 0   :=  by sorry
