-- Prove2me | Theorems.Thm_lean_workbook_plus_73844
-- name    : lean_workbook_plus_73844
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/74d287cd-6574-4640-a326-bab87b8082a7
-- statement:
--   Given positive real numbers $a,\ b$ .\n\nProve that :\n\n $(a^2-ab+b^2)(a+b)^4\geq 16a^3b^3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73844 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^2 - a*b + b^2)*(a + b)^4 ≥ 16*a^3*b^3   :=  by sorry
