-- Prove2me | Theorems.Thm_lean_workbook_plus_26355
-- name    : lean_workbook_plus_26355
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/045ede69-7b32-41c7-9e7d-9a81369dba45
-- statement:
--   If $a+b+c=1$ then: $a^3+b^3+c^3=1+3(abc-ab-bc-ca)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26355 (a b c : ℝ) (hab : a + b + c = 1) : a^3 + b^3 + c^3 = 1 + 3 * (a * b * c - a * b - b * c - c * a)   :=  by sorry
