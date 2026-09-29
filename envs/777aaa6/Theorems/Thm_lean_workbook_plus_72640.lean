-- Prove2me | Theorems.Thm_lean_workbook_plus_72640
-- name    : lean_workbook_plus_72640
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/ab7b41ee-f684-4326-a19d-838b02de4d09
-- statement:
--   From AM-GM, we have $ 2(a^2 + b^2 + c^2) \ge 2(ab + bc + ca) $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72640 (a b c : ℝ) : 2 * (a ^ 2 + b ^ 2 + c ^ 2) ≥ 2 * (a * b + b * c + c * a)   :=  by sorry
