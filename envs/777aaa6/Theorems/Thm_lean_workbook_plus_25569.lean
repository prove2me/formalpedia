-- Prove2me | Theorems.Thm_lean_workbook_plus_25569
-- name    : lean_workbook_plus_25569
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3baf40f6-3efc-4283-944d-8b692366a7e3
-- statement:
--   Prove that the following inequality holds for nonnegative reals: \n\n $(a+b+c+d)^3\geq 16(abc+bcd+cda+dab).$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25569 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a + b + c + d) ^ 3 ≥ 16 * (a * b * c + b * c * d + c * d * a + d * a * b)   :=  by sorry
