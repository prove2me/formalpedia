-- Prove2me | Theorems.Thm_lean_workbook_plus_3117
-- name    : lean_workbook_plus_3117
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/b01ebc8c-4120-4070-8583-3b71879be5cd
-- statement:
--   Let $x^2+y=K_1^2$ $y^2+x=k_2^2$ subtracting we get $(x-y)(x+y-1)=(k_1-k_2)(k_1+k_2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_3117 (x y : ℤ) (k_1 k_2 : ℤ) : (x^2 + y - (k_1^2)) - (y^2 + x - k_2^2) = (x - y) * (x + y - 1) - (k_1 - k_2) * (k_1 + k_2)   :=  by sorry
