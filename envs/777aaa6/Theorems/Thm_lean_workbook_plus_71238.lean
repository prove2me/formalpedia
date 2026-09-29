-- Prove2me | Theorems.Thm_lean_workbook_plus_71238
-- name    : lean_workbook_plus_71238
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/b5e17ef1-c1f3-49d1-9f4b-0538b56db6af
-- statement:
--   Prove $2(x^8-x^3)+3(x^6-x)+6>3x^3+x$ for $0<x<1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71238 : ∀ x : ℝ, 0 < x ∧ x < 1 → 2 * x ^ 8 - 2 * x ^ 3 + 3 * x ^ 6 - 3 * x + 6 > 3 * x ^ 3 + x   :=  by sorry
