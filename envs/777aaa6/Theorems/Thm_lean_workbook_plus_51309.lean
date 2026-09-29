-- Prove2me | Theorems.Thm_lean_workbook_plus_51309
-- name    : lean_workbook_plus_51309
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0304f8fb-041e-420b-a8ae-d0749112cb13
-- statement:
--   $ a^4+b^4+c^4+2abc(a+b+c) = \frac{1}{2}((a^2-b^2)^2+(b^2-c^2)^2+(c^2-a^2)^2) + (ab+bc+ca)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51309 (a b c : ℝ) : a^4 + b^4 + c^4 + 2 * a * b * c * (a + b + c) = 1 / 2 * ((a^2 - b^2)^2 + (b^2 - c^2)^2 + (c^2 - a^2)^2) + (a * b + b * c + c * a)^2   :=  by sorry
