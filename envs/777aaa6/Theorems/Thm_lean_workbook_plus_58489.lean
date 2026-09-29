-- Prove2me | Theorems.Thm_lean_workbook_plus_58489
-- name    : lean_workbook_plus_58489
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/a8ca616d-fd67-41da-b22f-9235f0447ff9
-- statement:
--   = \frac{3\cdot 2^5 - 3\cdot 1^5 + 1\cdot 0^5}{3^5} = \frac{96-3}{243} = \frac{31}{81}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58489 :
  (3 * 2^5 - 3 * 1^5 + 1 * 0^5) / 3^5 = 31 / 81   :=  by sorry
