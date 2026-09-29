-- Prove2me | Theorems.Thm_lean_workbook_plus_14910
-- name    : lean_workbook_plus_14910
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/7d8ee412-33f4-4595-b047-9ffc13ff4599
-- statement:
--   Given $0 \leq F_{X_1}(t) \leq F_{X_2}(t) \leq 1$ and $1 \geq 1-F_{X_1}(t) \geq 1-F_{X_2}(t) \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14910 (F_X1 F_X2 : ℝ → ℝ) (t : ℝ) (h1 : 0 ≤ F_X1 t ∧ 0 ≤ F_X2 t) (h2 : F_X1 t ≤ F_X2 t) (h3 : 1 ≥ 1 - F_X1 t ∧ 1 ≥ 1 - F_X2 t) (h4 : 1 - F_X1 t ≥ 1 - F_X2 t) : 0 ≤ F_X1 t ∧ 0 ≤ F_X2 t ∧ F_X1 t ≤ F_X2 t ∧ 1 ≥ 1 - F_X1 t ∧ 1 ≥ 1 - F_X2 t ∧ 1 - F_X1 t ≥ 1 - F_X2 t   :=  by sorry
