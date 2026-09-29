-- Prove2me | Theorems.Thm_lean_workbook_plus_81888
-- name    : lean_workbook_plus_81888
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/d3111ed7-7995-4dda-96f6-a43917b3da1c
-- statement:
--   $\sin{x}\cos{y}=\frac{1}{2}\cdot\left[\sin{\left(x+y\right)}+\sin{\left(x-y\right)}\right]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81888 (x y : ℝ) : sin x * cos y = 1 / 2 * (sin (x + y) + sin (x - y))   :=  by sorry
