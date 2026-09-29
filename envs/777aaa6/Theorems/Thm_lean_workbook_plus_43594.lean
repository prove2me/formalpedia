-- Prove2me | Theorems.Thm_lean_workbook_plus_43594
-- name    : lean_workbook_plus_43594
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/a648250b-a960-4b6a-a448-fdbd5169f7b2
-- statement:
--   prove that: $\left( a+b+c+d \right) \left( ab+bc+cd+ad \right) -4\,acd-4\,abd-4\,abc-4\,bcd= \left( b-d \right) ^{2}c+ \left( c-a \right) ^{2}d+ \left( d-b \right) ^{2}a+ \left( a-c \right) ^{2}b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43594  (a b c d : ℂ) :
  (a + b + c + d) * (a * b + b * c + c * d + d * a) - 4 * a * c * d - 4 * a * b * d - 4 * a * b * c - 4 * b * c * d = (b - d)^2 * c + (c - a)^2 * d + (d - b)^2 * a + (a - c)^2 * b   :=  by sorry
