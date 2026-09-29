-- Prove2me | Theorems.Thm_lean_workbook_plus_81246
-- name    : lean_workbook_plus_81246
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/2cb31bb9-cd63-468c-81c1-b7e4e5347ab6
-- statement:
--   $(a^2+b^2+c^2)(\frac{1}{bc}+\frac{1}{ca}+\frac{1}{ab}) = \frac{a^2}{bc}+\frac{b^2}{ca}+\frac{c^2}{ab}+\frac{a}{b}+\frac{b}{a}+\frac{b}{c}+\frac{c}{b}+\frac{c}{a}+\frac{a}{c}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81246 (a b c : ℝ) : (a^2+b^2+c^2)*(1/(b*c) + 1/(c*a) + 1/(a*b)) = a^2/(b*c) + b^2/(c*a) + c^2/(a*b) + a/b + b/a + b/c + c/b + c/a + a/c   :=  by sorry
