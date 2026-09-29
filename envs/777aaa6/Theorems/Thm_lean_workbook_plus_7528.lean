-- Prove2me | Theorems.Thm_lean_workbook_plus_7528
-- name    : lean_workbook_plus_7528
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/f6d81d08-84c0-4310-83a4-0bab7b85af08
-- statement:
--   prove $ xy+zx\leq x^2+\frac{y^2+z^2}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7528 (x y z : ℝ) : x * y + z * x ≤ x ^ 2 + (y ^ 2 + z ^ 2) / 2   :=  by sorry
