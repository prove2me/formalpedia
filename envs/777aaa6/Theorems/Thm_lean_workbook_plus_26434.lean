-- Prove2me | Theorems.Thm_lean_workbook_plus_26434
-- name    : lean_workbook_plus_26434
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/3a3d5bb8-29f3-4335-bd63-284b1121013d
-- statement:
--   prove that $ ab+bc+ca=(a+b)(b+c)+(b+c)(c+a)+(c+a)(a+b)-(a+b+c)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26434 (a b c : ℤ) : a * b + b * c + c * a = (a + b) * (b + c) + (b + c) * (c + a) + (c + a) * (a + b) - (a + b + c) ^ 2   :=  by sorry
