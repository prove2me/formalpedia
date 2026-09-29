-- Prove2me | Theorems.Thm_lean_workbook_plus_4122
-- name    : lean_workbook_plus_4122
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/5c4c81e0-97c4-45af-81e1-389b7b88161e
-- statement:
--   $ x^2 + y^2 = 2z^2 $ \n $ \Leftrightarrow (x+y)^2 + (x-y)^2 = (2z)^2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4122 (x y z : ℤ) : x^2 + y^2 = 2 * z^2 ↔ (x + y)^2 + (x - y)^2 = (2 * z)^2   :=  by sorry
