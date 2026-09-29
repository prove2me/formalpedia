-- Prove2me | Theorems.Thm_lean_workbook_plus_55638
-- name    : lean_workbook_plus_55638
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/f825827c-3941-4e24-b322-b8d752922258
-- statement:
--   Sketch the graph of $y = 3p^3 + 3p^2 - 3p$ and find its range for $-2 \leq p \leq \frac{2}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55638 (p : ℝ) (hp : -2 ≤ p ∧ p ≤ 2/3) : -6 ≤ 3 * p ^ 3 + 3 * p ^ 2 - 3 * p ∧ 3 * p ^ 3 + 3 * p ^ 2 - 3 * p ≤ 6   :=  by sorry
