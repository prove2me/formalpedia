-- Prove2me | Theorems.Thm_lean_workbook_plus_52998
-- name    : lean_workbook_plus_52998
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/ec16f76a-f44e-4a97-9c0e-fc3a05f82b31
-- statement:
--   prove that \((\frac{1+x^2}{1+x})^3\geq\frac{1+x^3}{2}\) for \(x\geq0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52998 (x : ℝ) (hx : 0 ≤ x) : (1 + x ^ 2) ^ 3 / (1 + x) ^ 3 ≥ (1 + x ^ 3) / 2   :=  by sorry
