-- Prove2me | Theorems.Thm_lean_workbook_plus_39387
-- name    : lean_workbook_plus_39387
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/e37d5ae2-1eed-433d-989d-f88d61786983
-- statement:
--   Check the solution: $x \in \left\{ x| \frac{\pi}{6}\leq x \leq \frac{5\pi}{6}, x\neq \frac{\pi}{4} \right\}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39387 (x : ℝ) : (x ∈ Set.Icc (π/6) (5*π/6) ∧ x ≠ π/4) ↔ (π/6) ≤ x ∧ x ≤ (5*π/6) ∧ x ≠ π/4   :=  by sorry
