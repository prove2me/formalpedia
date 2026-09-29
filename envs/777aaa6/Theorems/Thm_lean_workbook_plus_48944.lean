-- Prove2me | Theorems.Thm_lean_workbook_plus_48944
-- name    : lean_workbook_plus_48944
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/780d735f-3006-4e3b-8f94-0350a7606938
-- statement:
--   Prove that : \n\n $$\frac{a^{8061}}{a^2+1}+\frac{b^{29}}{b^2+1}+\frac{c^{121}}{c^2+1}+\frac{4101}{2}\geq 2015a^2+7b^2+30c^2.$$ \n\n Proposed by Kunihiko Chikaya
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48944 : ∀ a b c : ℝ, (a^8061 / (a^2 + 1) + b^29 / (b^2 + 1) + c^121 / (c^2 + 1) + 4101 / 2) ≥ 2015 * a^2 + 7 * b^2 + 30 * c^2   :=  by sorry
