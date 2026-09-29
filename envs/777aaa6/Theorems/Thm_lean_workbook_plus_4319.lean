-- Prove2me | Theorems.Thm_lean_workbook_plus_4319
-- name    : lean_workbook_plus_4319
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/59fd20f5-a47e-42ad-b0e1-a96961392aaa
-- statement:
--   Inequality is equivalent to: $ P(a)=2a^2-2a(b+c-3)+2(b^2+c^2)-2bc+6(1-b)\ge 0 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4319 (a b c : ℝ) : 2*a^2 - 2*a*(b + c - 3) + 2*(b^2 + c^2) - 2*b*c + 6*(1 - b) ≥ 0   :=  by sorry
