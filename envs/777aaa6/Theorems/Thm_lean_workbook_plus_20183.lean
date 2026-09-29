-- Prove2me | Theorems.Thm_lean_workbook_plus_20183
-- name    : lean_workbook_plus_20183
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/20b42366-d054-4b4c-a9e9-f2d2df1b0716
-- statement:
--   Let $ a,b>0$ and $ab=1 . $ Prove that \n $$ \frac{1}{a^2+b }+\frac{1}{b+1} \leq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20183 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) : 1 / (a^2 + b) + 1 / (b + 1) ≤ 1   :=  by sorry
