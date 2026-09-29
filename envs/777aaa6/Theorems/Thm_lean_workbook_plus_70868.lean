-- Prove2me | Theorems.Thm_lean_workbook_plus_70868
-- name    : lean_workbook_plus_70868
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/6e557627-f007-4a62-a9c9-45c58c805f2b
-- statement:
--   Let $ a, b>0$ and $a+b \geq 3 . $ Prove that \n $$ \left(a+\frac{1}{b}+1\right)\left(b+\frac{1}{a}+1\right) \geq 10$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70868 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b ≥ 3) : (a + 1 / b + 1) * (b + 1 / a + 1) ≥ 10   :=  by sorry
