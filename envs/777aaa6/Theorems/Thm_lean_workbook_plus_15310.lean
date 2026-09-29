-- Prove2me | Theorems.Thm_lean_workbook_plus_15310
-- name    : lean_workbook_plus_15310
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/323f0dbd-67cd-4833-9ce2-8b1355d38f62
-- statement:
--   $x \in \{2,\frac{1}{2}\log_{2}1022,\frac{1}{2}\log_{2}1023,5\}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15310 (x : ℝ) : x ∈ ({2, 1/2 * Real.logb 2 1022, 1/2 * Real.logb 2 1023, 5} : Set ℝ) ↔ x = 2 ∨ x = 1/2 * Real.logb 2 1022 ∨ x = 1/2 * Real.logb 2 1023 ∨ x = 5   :=  by sorry
