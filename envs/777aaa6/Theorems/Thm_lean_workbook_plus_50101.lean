-- Prove2me | Theorems.Thm_lean_workbook_plus_50101
-- name    : lean_workbook_plus_50101
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c9a73b1f-dc7b-43ba-bfd5-000ce98bd15e
-- statement:
--   substituting $a + b$ for y we get $cos^2a + cos^2b + cos^2(a + b) = 1 + 2cosacosbcos(a + b)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50101 : cos a ^ 2 + cos b ^ 2 + cos (a + b) ^ 2 = 1 + 2 * cos a * cos b * cos (a + b)   :=  by sorry
