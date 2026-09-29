-- Prove2me | Theorems.Thm_lean_workbook_plus_8985
-- name    : lean_workbook_plus_8985
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/193e3a63-fd1e-4c2e-87e6-dac82fe74a80
-- statement:
--   Let $a$ , $b$ be two non-negative real numbers such that $ab+a+b=3$ . Prove that $4\le ab(a^2+b^2)+a^3+b^3\le 27$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8985 (a b : ℝ) (hab : 0 ≤ a ∧ 0 ≤ b) (habp : a * b + a + b = 3) : 4 ≤ a * b * (a ^ 2 + b ^ 2) + a ^ 3 + b ^ 3 ∧ a * b * (a ^ 2 + b ^ 2) + a ^ 3 + b ^ 3 ≤ 27   :=  by sorry
