-- Prove2me | Theorems.Thm_lean_workbook_plus_7627
-- name    : lean_workbook_plus_7627
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/c1cca39b-2892-41a4-927a-58f1f733f828
-- statement:
--   Does $f(3x)^{4}$ equal $(f(3x))^{4}$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7627 (f : ℝ → ℝ) : (f (3 * x))^4 = f (3 * x)^4   :=  by sorry
