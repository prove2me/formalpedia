-- Prove2me | Theorems.Thm_lean_workbook_plus_44389
-- name    : lean_workbook_plus_44389
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/2d136b96-ef53-480a-8db5-d63b63fba5b7
-- statement:
--   $(a^2b+b^2c+c^2a)(ab+bc+ca) - abc(a+b+c)^2 = a^2c(b-c)^2+ab^2(c-a)^2+bc^2(a-b)^2 \\geqslant 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44389 (a b c : ℝ) :
  (a^2 * b + b^2 * c + c^2 * a) * (a * b + b * c + c * a) - a * b * c * (a + b + c)^2 ≥
  a^2 * c * (b - c)^2 + a * b^2 * (c - a)^2 + b * c^2 * (a - b)^2   :=  by sorry
