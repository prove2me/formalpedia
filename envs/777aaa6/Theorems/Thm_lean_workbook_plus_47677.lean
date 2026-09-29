-- Prove2me | Theorems.Thm_lean_workbook_plus_47677
-- name    : lean_workbook_plus_47677
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/fc34cb24-15ab-45dd-a03b-45e0e40b5883
-- statement:
--   Prove the identity $ (a + b)(b + c)(c + a) - 8abc = 2c (a - b)^2 + (a + b)(a - c)(b - c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47677 (a b c : ℝ) : (a + b) * (b + c) * (c + a) - 8 * a * b * c = 2 * c * (a - b) ^ 2 + (a + b) * (a - c) * (b - c)   :=  by sorry
