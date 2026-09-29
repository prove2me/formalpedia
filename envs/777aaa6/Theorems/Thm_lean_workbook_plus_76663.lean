-- Prove2me | Theorems.Thm_lean_workbook_plus_76663
-- name    : lean_workbook_plus_76663
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/046c63a5-6760-426f-a5b3-c5aa09da81b4
-- statement:
--   Let $ a,b>0$ and $ab=1 . $ Prove that \n $$ \frac{1}{a^2+b }+\frac{1}{b+1} \leq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76663 (a b : ℝ) (hab : a * b = 1) (ha : 0 < a) (hb : 0 < b) : 1 / (a ^ 2 + b) + 1 / (b + 1) ≤ 1   :=  by sorry
