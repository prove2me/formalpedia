-- Prove2me | Theorems.Thm_lean_workbook_plus_40199
-- name    : lean_workbook_plus_40199
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d1b8853f-9be8-4b6c-b0b6-f41673822441
-- statement:
--   Prove that $(1+a)(1+b)(1+c)$ ≥ $8(1-a)(1-b)(1-c)$ given $a+b+c=1$ and $a, b, c > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40199 : a + b + c = 1 ∧ a > 0 ∧ b > 0 ∧ c > 0 → (1 + a) * (1 + b) * (1 + c) ≥ 8 * (1 - a) * (1 - b) * (1 - c)   :=  by sorry
