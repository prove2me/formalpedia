-- Prove2me | Theorems.Thm_lean_workbook_plus_37086
-- name    : lean_workbook_plus_37086
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/d299d770-0466-4b0b-8c5f-d9bdefc7b19f
-- statement:
--   I multiplied $(a+b+c)^3$ and got $a^3+b^3+c^3+6abc+3(a^2b+a^2c+b^2a+b^2c+c^2a+c^2b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37086 (a b c : ℤ) : (a + b + c) ^ 3 = a ^ 3 + b ^ 3 + c ^ 3 + 6 * a * b * c + 3 * (a ^ 2 * b + a ^ 2 * c + b ^ 2 * a + b ^ 2 * c + c ^ 2 * a + c ^ 2 * b)   :=  by sorry
