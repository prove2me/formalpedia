-- Prove2me | Theorems.Thm_lean_workbook_plus_78633
-- name    : lean_workbook_plus_78633
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/f102fe66-d5b2-4d13-b2d4-e3df097b2591
-- statement:
--   $x_ix_{i+1} \leq \frac{{x_i}^2+{x_{i+1}}^2}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78633 (x : ℕ → ℝ) (i : ℕ) : x i * x (i + 1) ≤ (x i ^ 2 + x (i + 1) ^ 2) / 2   :=  by sorry
