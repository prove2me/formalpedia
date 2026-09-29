-- Prove2me | Theorems.Thm_lean_workbook_plus_32182
-- name    : lean_workbook_plus_32182
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/40740a42-d461-453d-8176-cba2fc182d6b
-- statement:
--   Compute $(1 - 2(3 - 4(5 - 6)))(7 - (8 - 9))$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32182 : (1 - 2 * (3 - 4 * (5 - 6))) * (7 - (8 - 9)) = -104   :=  by sorry
