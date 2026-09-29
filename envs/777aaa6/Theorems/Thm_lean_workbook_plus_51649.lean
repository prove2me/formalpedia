-- Prove2me | Theorems.Thm_lean_workbook_plus_51649
-- name    : lean_workbook_plus_51649
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/289aa509-7348-4bed-932b-70d3a8637657
-- statement:
--   For $a, b, c>0$ prove that \n $\frac{a}{5a+2b+c}+\frac{b}{a+5b+2c}+\frac{c}{2a+b+5c}\leq\frac{3}{8}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51649 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a / (5 * a + 2 * b + c) + b / (a + 5 * b + 2 * c) + c / (2 * a + b + 5 * c) ≤ 3 / 8)   :=  by sorry
