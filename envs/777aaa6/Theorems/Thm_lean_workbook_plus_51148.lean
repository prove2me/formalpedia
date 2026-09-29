-- Prove2me | Theorems.Thm_lean_workbook_plus_51148
-- name    : lean_workbook_plus_51148
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/9081fcc4-3446-45e5-aced-e5661785b4f7
-- statement:
--   Prove $x^2-x(1+y)+y^2-y+1 \geq 0$ where $x = \sin(a)$ and $y = \sin(b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51148 (a b : ℝ) : (sin a)^2 - sin a * (1 + sin b) + (sin b)^2 - sin b + 1 ≥ 0   :=  by sorry
