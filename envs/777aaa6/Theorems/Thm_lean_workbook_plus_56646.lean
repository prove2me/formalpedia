-- Prove2me | Theorems.Thm_lean_workbook_plus_56646
-- name    : lean_workbook_plus_56646
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/e463ffba-b1f0-4e02-bfc2-a4c05cff7998
-- statement:
--   Prove that \((a + b)\left(\frac{1}{a} + \frac{1}{b}\right) \geq 4\) for positive \(a\) and \(b\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56646 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a + b) * (1 / a + 1 / b) ≥ 4   :=  by sorry
