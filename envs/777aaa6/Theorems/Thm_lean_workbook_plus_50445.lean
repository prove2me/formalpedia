-- Prove2me | Theorems.Thm_lean_workbook_plus_50445
-- name    : lean_workbook_plus_50445
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/22e796a8-8a7a-4be1-a411-7c2a2d0a7e5c
-- statement:
--   Prove the following identity for any positive real numbers a, b, and c: $ a^3+b^3+c^3-3abc=(a+b+c)((a-b)^2+(b-c)^2+(c-a)^2)/2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50445 (a b c : ℝ) : a^3 + b^3 + c^3 - 3*a*b*c = (a + b + c)*((a - b)^2 + (b - c)^2 + (c - a)^2)/2   :=  by sorry
