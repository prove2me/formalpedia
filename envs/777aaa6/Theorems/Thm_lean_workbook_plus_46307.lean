-- Prove2me | Theorems.Thm_lean_workbook_plus_46307
-- name    : lean_workbook_plus_46307
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/eeff0de9-a02a-4653-b656-1a7bae6a803d
-- statement:
--   Prove the second inequality: $\ln(x) \leq x - 1$ for $x \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46307 (x : ℝ) (hx : 1 ≤ x) : Real.log x ≤ x - 1   :=  by sorry
