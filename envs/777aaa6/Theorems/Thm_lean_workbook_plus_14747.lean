-- Prove2me | Theorems.Thm_lean_workbook_plus_14747
-- name    : lean_workbook_plus_14747
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/00ac6917-2edc-44df-8099-cd3c29034c19
-- statement:
--   Given $ a,b,c \ge 0$ Prove that $ a^2 + b^2 + c^2 - ab - bc - ca = \frac{(a-b)^2+(b-c)^2+(c-a)^2}{2} \ge 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14747 (a b c : ℝ) : a^2 + b^2 + c^2 - (a * b + b * c + c * a) = (1/2) * ( (a - b)^2 + (b - c)^2 + (c - a)^2)   :=  by sorry
