-- Prove2me | Theorems.Thm_lean_workbook_plus_72778
-- name    : lean_workbook_plus_72778
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/2fed583f-29fd-4db2-9501-3fd4431af24f
-- statement:
--   Prove the identity $ a^2 b^2 + b^2 c^2 + c^2 a^2 - abc (a + b + c) = c^2 (a - b)^2 + ab (a - c)(b - c) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72778 (a b c : ℤ) : a^2 * b^2 + b^2 * c^2 + c^2 * a^2 - a * b * c * (a + b + c) = c^2 * (a - b)^2 + a * b * (a - c) * (b - c)   :=  by sorry
