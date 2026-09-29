-- Prove2me | Theorems.Thm_lean_workbook_plus_64435
-- name    : lean_workbook_plus_64435
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/52ac9193-a2f2-4a23-8196-ff2814d00b0f
-- statement:
--   Now we have $ (a+b)^2 - 4ab = (c+d)^2 -4cd \Leftrightarrow (a-b)^2=(c-d)^2 \Leftrightarrow $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64435 (a b c d : ℤ) : (a+b)^2 - 4*a*b = (c+d)^2 - 4*c*d ↔ (a-b)^2 = (c-d)^2   :=  by sorry
