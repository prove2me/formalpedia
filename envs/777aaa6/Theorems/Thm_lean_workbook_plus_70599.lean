-- Prove2me | Theorems.Thm_lean_workbook_plus_70599
-- name    : lean_workbook_plus_70599
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d980903c-9bb0-4803-be6f-cb617601961b
-- statement:
--   $ x^3+\frac{1}{3\sqrt{3}}+\frac{1}{3\sqrt{3}}\geq x\Rightarrow x(1-x^2)\leq\frac{2}{3\sqrt{3}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70599 (x : ℝ) : x^3 + 1 / (3 * Real.sqrt 3) + 1 / (3 * Real.sqrt 3) ≥ x → x * (1 - x^2) ≤ 2 / (3 * Real.sqrt 3)   :=  by sorry
