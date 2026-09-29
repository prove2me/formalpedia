-- Prove2me | Theorems.Thm_lean_workbook_plus_81049
-- name    : lean_workbook_plus_81049
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/cf19dc4a-7d4b-4aaa-b113-7aca0a7c7339
-- statement:
--   Prove that $e^{-x}>0$ for all $x\ge0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81049 : ∀ x : ℝ, x ≥ 0 → exp (-x) > 0   :=  by sorry
