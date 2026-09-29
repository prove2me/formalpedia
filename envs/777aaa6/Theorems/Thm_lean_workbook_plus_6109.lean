-- Prove2me | Theorems.Thm_lean_workbook_plus_6109
-- name    : lean_workbook_plus_6109
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f075ce42-80cb-4318-b7a3-cc5c8c41387b
-- statement:
--   Let $x_j=a_j+b_ji(1\leq j\leq n)$ ,then we have $\sum_{j=1}^n |x_j|\geq |\sum_{j=1}^n x_j|.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6109 (n : ℕ) (x : ℕ → ℂ) : ∑ j in Finset.range n, ‖x j‖ ≥ ‖∑ j in Finset.range n, x j‖   :=  by sorry
