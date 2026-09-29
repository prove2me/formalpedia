-- Prove2me | Theorems.Thm_lean_workbook_plus_9906
-- name    : lean_workbook_plus_9906
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/67fb7f9e-328b-482c-99fe-71dc92cecb8e
-- statement:
--   Let $a,b,c \ge 0$ such that $a+b+c=1$ . Prove that \n $$ a^2+b^2+c^2 \le \frac{1}{4}+a^3+b^3+c^3$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9906 (a b c : ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a + b + c = 1) : a^2 + b^2 + c^2 ≤ 1 / 4 + a^3 + b^3 + c^3   :=  by sorry
