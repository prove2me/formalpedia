-- Prove2me | Theorems.Thm_lean_workbook_plus_10183
-- name    : lean_workbook_plus_10183
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/130cb20f-2b5a-413b-b120-765d5e5646de
-- statement:
--   If $y=3(mod4)$, then $y^3+27=2(mod4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10183 : ∀ y : ℤ, y % 4 = 3 → (y^3 + 27) % 4 = 2   :=  by sorry
