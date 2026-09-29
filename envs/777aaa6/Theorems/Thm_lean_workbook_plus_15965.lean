-- Prove2me | Theorems.Thm_lean_workbook_plus_15965
-- name    : lean_workbook_plus_15965
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/f69a9ccc-2ad0-4132-be2a-4f691fec2135
-- statement:
--   Prove that $(a-b)^2 \geq 0 \implies ab \leq \frac{1}{2}a^2 + \frac{1}{2} b^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15965 (a b : ℝ) (h : (a - b) ^ 2 ≥ 0) :
  a * b ≤ 1 / 2 * a ^ 2 + 1 / 2 * b ^ 2   :=  by sorry
