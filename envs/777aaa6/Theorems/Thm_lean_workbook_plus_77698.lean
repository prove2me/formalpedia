-- Prove2me | Theorems.Thm_lean_workbook_plus_77698
-- name    : lean_workbook_plus_77698
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/98b3ad77-7068-446c-a0cb-8745f0afd329
-- statement:
--   $(a+b\sqrt{3})^3=(a^3+9ab^2)+(3a^2b+3b^3)\sqrt{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77698 : (a + b * Real.sqrt 3)^3 = (a^3 + 9 * a * b^2) + (3 * a^2 * b + 3 * b^3) * Real.sqrt 3   :=  by sorry
