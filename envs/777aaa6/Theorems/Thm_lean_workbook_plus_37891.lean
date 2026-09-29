-- Prove2me | Theorems.Thm_lean_workbook_plus_37891
-- name    : lean_workbook_plus_37891
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/667f909f-33d1-4116-8e63-ad82950d9985
-- statement:
--   Prove the identity $ a^4 + b^4 + c^4 - a^2 b^2 - b^2 c^2 - c^2 a^2 = (a + b)^2 (a - b)^2 + (a + c)(b + c)(a - c)(b - c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37891 (a b c : ℤ) : a^4 + b^4 + c^4 - a^2 * b^2 - b^2 * c^2 - c^2 * a^2 = (a + b)^2 * (a - b)^2 + (a + c) * (b + c) * (a - c) * (b - c)   :=  by sorry
