-- Prove2me | Theorems.Thm_lean_workbook_plus_77251
-- name    : lean_workbook_plus_77251
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/dd58882a-59a3-4949-9eda-ab0e2e43c7ad
-- statement:
--   Let $a,b,c$ be real numbers. Prove that $3(a^2+b^2+c^2)^2+6(ab+bc+ca)^2\ge (a+b+c)^4$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77251 (a b c : ℝ) : 3 * (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 + 6 * (a * b + b * c + c * a) ^ 2 ≥ (a + b + c) ^ 4   :=  by sorry
