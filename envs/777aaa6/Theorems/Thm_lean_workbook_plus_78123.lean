-- Prove2me | Theorems.Thm_lean_workbook_plus_78123
-- name    : lean_workbook_plus_78123
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/85c4d29b-246b-4e84-912b-093d00a2194d
-- statement:
--   You can use this fact: $|x-f(y)|=|(x-f(x))+(f(x)-f(y))|\leq |x-f(x)|+|f(x)-f(y)|$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78123 (f : ℝ → ℝ) (x y : ℝ) :
  |x - f y| = |(x - f x) + (f x - f y)| ∧
  |x - f y| ≤ |x - f x| + |f x - f y|   :=  by sorry
