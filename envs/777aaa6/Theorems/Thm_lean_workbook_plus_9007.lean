-- Prove2me | Theorems.Thm_lean_workbook_plus_9007
-- name    : lean_workbook_plus_9007
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/61035297-5e53-4a3a-a97f-aa68bc1ccf16
-- statement:
--   Find the roots of the polynomial $x^{4} -12x^{3} +49x^{2} -78x +40$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9007 (x : ℂ) : x^4 - 12*x^3 + 49*x^2 - 78*x + 40 = 0 ↔ x = 1 ∨ x = 2 ∨ x = 4 ∨ x = 5   :=  by sorry
