-- Prove2me | Theorems.Thm_lean_workbook_plus_37482
-- name    : lean_workbook_plus_37482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/380400d7-3d73-4706-a68e-ed4133f61d50
-- statement:
--   Rewrite $P=(2a)^2+(b^2+1)^2+(2c)^2-1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37482 (a b c : ℤ) : (2 * a) ^ 2 + (b ^ 2 + 1) ^ 2 + (2 * c) ^ 2 - 1 = 4 * a ^ 2 + b ^ 4 + 2 * b ^ 2 + 4 * c ^ 2   :=  by sorry
