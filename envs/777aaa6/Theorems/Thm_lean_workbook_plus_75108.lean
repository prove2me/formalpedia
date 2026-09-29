-- Prove2me | Theorems.Thm_lean_workbook_plus_75108
-- name    : lean_workbook_plus_75108
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/dfe5cf3d-5bbb-4dcd-b0bc-051d9a5a5cd6
-- statement:
--   Let $f(x) = x - \frac{1}{x}$, prove that $f$ is an increasing function for $x > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75108 (x y : ℝ) (h₁ : x > 0 ∧ y > 0) (h₂ : x < y) : x - 1/x < y - 1/y   :=  by sorry
