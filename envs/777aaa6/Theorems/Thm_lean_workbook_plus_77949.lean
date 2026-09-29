-- Prove2me | Theorems.Thm_lean_workbook_plus_77949
-- name    : lean_workbook_plus_77949
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/a0871e3c-4b6f-48da-acac-596c00d52fb0
-- statement:
--   Compute the value of the expression: \n $\frac{2011^3-2000^3-11^3}{(2011)(2000)(11)}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77949 (h₁ : 2011 ≠ 0 ∧ 2000 ≠ 0 ∧ 11 ≠ 0) : (2011^3 - 2000^3 - 11^3) / (2011 * 2000 * 11) = 3   :=  by sorry
