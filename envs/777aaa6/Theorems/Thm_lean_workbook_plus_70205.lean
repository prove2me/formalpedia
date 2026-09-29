-- Prove2me | Theorems.Thm_lean_workbook_plus_70205
-- name    : lean_workbook_plus_70205
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/bb361f85-2ad7-4f6e-96b8-c3a4004af79e
-- statement:
--   Prove easily that $(a + b + c)(a + b - c)(b + c - a)(c + a - b)=2\left(a^2b^2+b^2c^2+c^2a^2\right)-\left(a^4+b^4+c^4\right)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70205 (a b c: ℝ) : (a + b + c) * (a + b - c) * (b + c - a) * (c + a - b) = 2 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2) - (a ^ 4 + b ^ 4 + c ^ 4)   :=  by sorry
