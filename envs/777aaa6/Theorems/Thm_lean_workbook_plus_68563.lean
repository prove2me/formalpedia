-- Prove2me | Theorems.Thm_lean_workbook_plus_68563
-- name    : lean_workbook_plus_68563
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/bec536b3-448e-4f52-a1a0-70929ca755c3
-- statement:
--   We can see, that $(a+b+c)^3-a^3-b^3-c^3 = 3(a + b)(b + c)(c + a);$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68563  (a b c : ℝ) :
  (a + b + c) ^ 3 - a ^ 3 - b ^ 3 - c ^ 3 = 3 * (a + b) * (b + c) * (c + a)   :=  by sorry
