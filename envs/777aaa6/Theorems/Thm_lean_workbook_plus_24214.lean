-- Prove2me | Theorems.Thm_lean_workbook_plus_24214
-- name    : lean_workbook_plus_24214
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/69a02931-a886-4450-b286-8cd5c4f16d56
-- statement:
--   Let $x=a+b+c,y=ab+bc+ca,$ then $x^2 \ge 3y$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24214 (x y : ℝ) (hx: x = a+b+c) (hy: y = a*b+b*c+c*a): x^2 >= 3*y   :=  by sorry
