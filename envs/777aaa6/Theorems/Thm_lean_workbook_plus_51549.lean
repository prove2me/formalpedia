-- Prove2me | Theorems.Thm_lean_workbook_plus_51549
-- name    : lean_workbook_plus_51549
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/237c1521-2ea0-4131-b724-fe642e0ff9a4
-- statement:
--   $2\sqrt m (\sqrt m +\sqrt n)\frac{\sqrt m +\sqrt n}{2\sqrt m}=(\sqrt m +\sqrt n)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51549 (m n : ℝ) (h₁ : m ≥ 0 ∧ n ≥ 0) (h₂ : m ≠ 0) : 2 * Real.sqrt m * (Real.sqrt m + Real.sqrt n) * (Real.sqrt m + Real.sqrt n) / (2 * Real.sqrt m) = (Real.sqrt m + Real.sqrt n) ^ 2   :=  by sorry
