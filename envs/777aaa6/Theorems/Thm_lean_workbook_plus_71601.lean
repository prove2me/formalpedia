-- Prove2me | Theorems.Thm_lean_workbook_plus_71601
-- name    : lean_workbook_plus_71601
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/db77ac0a-23de-4469-a323-d41ee49ff387
-- statement:
--   We can find that $f(x)=x(\frac{2}{3}-x)+(1-x)(x-\frac{1}{2})=\frac{2}{3}x-x^2-x^2+x+\frac{1}{2}x-\frac{1}{2}=-2x^2+\frac{13}{6}x-\frac{1}{2},$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71601  (x : ℝ) :
  x * (2 / 3 - x) + (1 - x) * (x - 1 / 2) = -2 * x^2 + (13 / 6) * x - 1 / 2   :=  by sorry
