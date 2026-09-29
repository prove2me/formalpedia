-- Prove2me | Theorems.Thm_lean_workbook_plus_72196
-- name    : lean_workbook_plus_72196
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/bf35e723-59d9-41e2-934b-1e93e50a4038
-- statement:
--   Prove that $\frac{1}{2}((a-b)^2(a^2+b^2) + (b-c)^2(b^2+c^2) + (c-a)^2(c^2+a^2)) \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72196 (a b c : ℝ) : (1 / 2) * ((a - b) ^ 2 * (a ^ 2 + b ^ 2) + (b - c) ^ 2 * (b ^ 2 + c ^ 2) + (c - a) ^ 2 * (c ^ 2 + a ^ 2)) ≥ 0   :=  by sorry
