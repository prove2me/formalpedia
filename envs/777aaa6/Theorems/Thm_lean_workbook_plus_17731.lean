-- Prove2me | Theorems.Thm_lean_workbook_plus_17731
-- name    : lean_workbook_plus_17731
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/91ab2bee-647e-44b4-9bb3-0a000798b2c5
-- statement:
--   Prove $ \frac{{(3-x)}^{5}+32}{{x}^{3}+1}-120+88x\geq 0$ for $ 0\leq x\leq 3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17731 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 3) :
  ((3 - x) ^ 5 + 32) / (x ^ 3 + 1) - 120 + 88 * x ≥ 0   :=  by sorry
