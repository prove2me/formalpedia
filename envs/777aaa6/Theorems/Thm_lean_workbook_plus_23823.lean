-- Prove2me | Theorems.Thm_lean_workbook_plus_23823
-- name    : lean_workbook_plus_23823
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/263b7e0a-9193-48c1-bf72-7d3548f4cbc5
-- statement:
--   Equivalent to prove that \n\n $$ \frac23(a^2+b^2+c^2)^2+abc(a+b+c) \ge (a^2+b^2+c^2)(ab+bc+ca) $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23823 {a b c : ℝ} : (2 / 3) * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + a * b * c * (a + b + c) ≥ (a ^ 2 + b ^ 2 + c ^ 2) * (a * b + b * c + a * c)   :=  by sorry
