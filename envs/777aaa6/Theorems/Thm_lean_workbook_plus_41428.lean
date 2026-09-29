-- Prove2me | Theorems.Thm_lean_workbook_plus_41428
-- name    : lean_workbook_plus_41428
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/bcc380cb-81d8-4e97-badf-cb0ec84bb71c
-- statement:
--   Prove the inequality $\ln\left(1+\frac{nx}{n+1}\right) \le \ln\left(1+\frac{n}{n+1}\right)$ for $x \in [0,1]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_41428 (n : ℕ) (x : ℝ) (hx : 0 ≤ x ∧ x ≤ 1) :
  Real.log (1 + n * x / (n + 1)) ≤ Real.log (1 + n / (n + 1))   :=  by sorry
