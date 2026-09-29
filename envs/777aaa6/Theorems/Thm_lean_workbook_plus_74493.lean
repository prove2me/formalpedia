-- Prove2me | Theorems.Thm_lean_workbook_plus_74493
-- name    : lean_workbook_plus_74493
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/62711a37-fb18-47a0-8c4b-f0641f84029b
-- statement:
--   $ 6t^{2}-77t+147\\leq 0$ ---> $ \\frac{7}{3}\\leq t \leq 10.5$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74493 (t : ℝ) : 6 * t ^ 2 - 77 * t + 147 ≤ 0 ↔ 7 / 3 ≤ t ∧ t ≤ 10.5   :=  by sorry
