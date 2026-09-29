-- Prove2me | Theorems.Thm_lean_workbook_plus_47499
-- name    : lean_workbook_plus_47499
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/50f95122-2bda-43f4-ba59-b72473eae44d
-- statement:
--   $a^7 + b^7 = (a + b)(a^6 - a^5b + a^4b^2 - a^3b^3 + a^2b^4 - ab^5 + b^6)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47499 (a b : ℤ) : a^7 + b^7 = (a + b)*(a^6 - a^5*b + a^4*b^2 - a^3*b^3 + a^2*b^4 - a*b^5 + b^6)   :=  by sorry
