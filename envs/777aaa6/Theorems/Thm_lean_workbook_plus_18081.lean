-- Prove2me | Theorems.Thm_lean_workbook_plus_18081
-- name    : lean_workbook_plus_18081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/05ae330e-5344-4df8-a494-0318214147a4
-- statement:
--   The following inequality is also true. \nGiven $a,b,c$ are positive integers satisfying $a+b+c=\frac{1}{a}+\frac{1}{b}+\frac{1}{c}$ .Prove that \n $$ bc+ca+ab+abc \geq 4.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18081 (a b c : ℕ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (hab : a + b + c = 1 / a + 1 / b + 1 / c) : a * b + b * c + c * a + a * b * c ≥ 4   :=  by sorry
