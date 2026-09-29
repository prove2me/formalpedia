-- Prove2me | Theorems.Thm_lean_workbook_plus_40978
-- name    : lean_workbook_plus_40978
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6f3cfa7d-1930-4d7f-be50-9667bb9478b6
-- statement:
--   Note that $b^4+4a^4=(2a^2-2ab+b^2)(2a^2+2ab+b^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40978 : ∀ a b : ℤ, b^4+4*a^4 = (2*a^2-2*a*b+b^2) * (2*a^2+2*a*b+b^2)   :=  by sorry
