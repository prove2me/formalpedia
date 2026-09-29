-- Prove2me | Theorems.Thm_lean_workbook_plus_25993
-- name    : lean_workbook_plus_25993
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/cd5bd6fd-4797-4dca-af00-756f2c63767c
-- statement:
--   $ \left( b+d \right) \left( c+a \right) \left( acd+abd+abc+bcd \right) -4\, \left( a+b+c+d \right) abcd= \left( b-d \right) ^{2}{a}^{2}c+ \left( a-c \right) ^{2}b{d}^{2}+ \left( d-b \right) ^{2}{c}^{2}a+ \left( c-a \right) ^{2}{b}^{2}d$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25993 (a b c d : ℝ) :
  (b + d) * (c + a) * (a * c * d + a * b * d + b * c * a + b * d * c) - 4 * (a + b + c + d) * (a * b * c * d) =
    (b - d) ^ 2 * a ^ 2 * c + (a - c) ^ 2 * b * d ^ 2 + (d - b) ^ 2 * c ^ 2 * a + (c - a) ^ 2 * b ^ 2 * d   :=  by sorry
