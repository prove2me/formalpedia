-- Prove2me | Theorems.Thm_lean_workbook_plus_41254
-- name    : lean_workbook_plus_41254
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/3101bdc5-8396-4d85-9cea-f6763f276959
-- statement:
--   Prove that $f(x) = x$ for $x \geq 0$ and $f(x) = 0$ for $x \leq 0$ is a solution to the given functional equation.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41254 (f : ℝ → ℝ) (hf: f x = if x ≥ 0 then x else 0) : f x = if x ≥ 0 then x else 0   :=  by sorry
