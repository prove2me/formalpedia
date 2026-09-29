-- Prove2me | Theorems.Thm_lean_workbook_plus_39686
-- name    : lean_workbook_plus_39686
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/2768658c-dbd1-441e-b32c-89fa3471aa65
-- statement:
--   Prove that $\frac{1-x}{x^2 + 4x + 20} \le \frac{1-x}{20}$ for all $x \in [0,1]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39686 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
  (1 - x) / (x ^ 2 + 4 * x + 20) ≤ (1 - x) / 20   :=  by sorry
