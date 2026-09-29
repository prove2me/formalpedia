-- Prove2me | Theorems.Thm_lean_workbook_plus_29447
-- name    : lean_workbook_plus_29447
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/f10ef02c-9c09-4b6f-9425-8d117ace08e8
-- statement:
--   Prove that $x + \frac{1}{x^2} \geq 2$ for $x \in (0, 1]$ using the Arithmetic Mean-Geometric Mean (AM-GM) inequality.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29447 (x : ℝ) (hx : 0 < x ∧ x ≤ 1) :
  x + (1 / x ^ 2) ≥ 2   :=  by sorry
