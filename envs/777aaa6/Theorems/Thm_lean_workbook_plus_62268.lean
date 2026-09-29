-- Prove2me | Theorems.Thm_lean_workbook_plus_62268
-- name    : lean_workbook_plus_62268
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/9d45ed1a-0cdd-49d5-b043-59c7f5b97336
-- statement:
--   Prove that \(1\geq\frac{x+y+z}{3}\) using the arithmetic mean-geometric mean inequality (AM-QM) given \(x^2+y^2+z^2=3\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62268 (x y z : ℝ) (hx : x ^ 2 + y ^ 2 + z ^ 2 = 3) : 1 ≥ (x + y + z) / 3   :=  by sorry
