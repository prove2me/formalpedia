-- Prove2me | Theorems.Thm_lean_workbook_plus_54866
-- name    : lean_workbook_plus_54866
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/7fd869a8-fe37-49d1-bd58-e228d4630795
-- statement:
--   Prove that $(x+y)(y+z)(z+x)(x+y+z)\geq x(y+z)^{3}+y(z+x)^{3}+z(x+y)^{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54866 (x y z : ℝ) : (x + y) * (y + z) * (z + x) * (x + y + z) ≥ x * (y + z) ^ 3 + y * (z + x) ^ 3 + z * (x + y) ^ 3   :=  by sorry
