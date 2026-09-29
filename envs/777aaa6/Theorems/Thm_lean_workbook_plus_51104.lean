-- Prove2me | Theorems.Thm_lean_workbook_plus_51104
-- name    : lean_workbook_plus_51104
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/05e7b36a-7a20-4ed3-8f3a-b0339027f7ce
-- statement:
--   $x_ix_{i+2} \leq \frac{{x_i}^2+{x_{i+2}}^2}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51104 (x : ℕ → ℝ) (i : ℕ) :
  x i * x (i + 2) ≤ (x i ^ 2 + x (i + 2) ^ 2) / 2   :=  by sorry
