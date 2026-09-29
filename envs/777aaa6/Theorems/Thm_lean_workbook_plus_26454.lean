-- Prove2me | Theorems.Thm_lean_workbook_plus_26454
-- name    : lean_workbook_plus_26454
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/ea1622fb-89cc-404b-86dc-332a4e3c1025
-- statement:
--   Factor $x^{6}(x^{2}+x+1)+2x^{3}(x^{2}+x+1)+3(x^{2}+x+1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26454 (x : ℤ) : x^6 * (x^2 + x + 1) + 2 * x^3 * (x^2 + x + 1) + 3 * (x^2 + x + 1) = (x^2 + x + 1) * (x^6 + 2 * x^3 + 3)   :=  by sorry
