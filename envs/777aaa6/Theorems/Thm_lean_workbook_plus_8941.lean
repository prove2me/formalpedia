-- Prove2me | Theorems.Thm_lean_workbook_plus_8941
-- name    : lean_workbook_plus_8941
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/f2d4274d-0efb-4c3e-8c4b-f1b8b7c26036
-- statement:
--   Let $a>1,b>1$ , prove that \n $\frac{a^2}{b-1}+\frac{b^2}{a-1}\ge 8$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8941 (a b : ℝ) (ha : 1 < a) (hb : 1 < b) : a^2 / (b - 1) + b^2 / (a - 1) ≥ 8   :=  by sorry
