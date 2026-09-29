-- Prove2me | Theorems.Thm_lean_workbook_plus_8922
-- name    : lean_workbook_plus_8922
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3ff9609e-1223-4c13-9e39-4f13286b4852
-- statement:
--   Prove $n(x^2 - 1)^2(2x^n + 1) + 2x^n(x^4 + 4x^2 + 3) + 2(x^4 - 1) \geq 0$ for $x \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8922 (n : ℕ) (x : ℝ) (hx: x >= 1): n * (x ^ 2 - 1) ^ 2 * (2 * x ^ n + 1) + 2 * x ^ n * (x ^ 4 + 4 * x ^ 2 + 3) + 2 * (x ^ 4 - 1) ≥ 0   :=  by sorry
