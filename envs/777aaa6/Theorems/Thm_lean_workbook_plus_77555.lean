-- Prove2me | Theorems.Thm_lean_workbook_plus_77555
-- name    : lean_workbook_plus_77555
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/b0ed07ef-5b7e-4650-82da-097f12646cd8
-- statement:
--   $\Leftrightarrow 12pr \geq 2(4q-p^2)(p^2-q)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77555 {p q r : ℝ} (hp : p > 0 ∧ q > 0 ∧ r > 0) (hpq : p + q + r = 1) (hpqr : p * q * r = 1) : 12 * p * q * r ≥ 2 * (4 * q - p ^ 2) * (p ^ 2 - q)   :=  by sorry
