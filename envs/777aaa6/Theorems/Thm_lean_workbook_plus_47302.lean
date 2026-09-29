-- Prove2me | Theorems.Thm_lean_workbook_plus_47302
-- name    : lean_workbook_plus_47302
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/d4d72d02-aa3d-4e6a-aa71-05e091880c52
-- statement:
--   Prove the triangle inequality: $|a| - |b| \le |a+b| \le |a| + |b|$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47302 (a b : ℝ) : |a| - |b| ≤ |a + b| ∧ |a + b| ≤ |a| + |b|   :=  by sorry
