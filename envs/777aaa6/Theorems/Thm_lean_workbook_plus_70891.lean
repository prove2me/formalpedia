-- Prove2me | Theorems.Thm_lean_workbook_plus_70891
-- name    : lean_workbook_plus_70891
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/d2972ee5-b712-4e71-855d-97297de8ed1e
-- statement:
--   Or : \n\n $(p+q)^3 = 4*(p^3 + q^3) - 3*(p+q)*(p-q)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70891 (p q : ℝ) : (p + q) ^ 3 = 4 * (p ^ 3 + q ^ 3) - 3 * (p + q) * (p - q) ^ 2   :=  by sorry
