-- Prove2me | Theorems.Thm_lean_workbook_plus_23586
-- name    : lean_workbook_plus_23586
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/a9aab73a-005f-4f5e-bcf9-f3ae3c1d205b
-- statement:
--   Prove that \(\frac{a}{a+c-b}+1\geq 2\sqrt{\frac{a}{a+c-b}}\) assuming \(\frac{a}{a+c-b}\geq 0\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23586 (a b c : ℝ) (h : a / (a + c - b) ≥ 0) :
  a / (a + c - b) + 1 ≥ 2 * Real.sqrt (a / (a + c - b))   :=  by sorry
