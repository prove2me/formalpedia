-- Prove2me | Theorems.Thm_lean_workbook_plus_28391
-- name    : lean_workbook_plus_28391
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/1c15be30-4d5f-4b07-bbba-4e4928a897c2
-- statement:
--   $\cos{\left(2x\right)}={\cos}^2{\left(x\right)}-{\sin}^2{x}=2{\cos}^2{x}-1=1-2{\sin}^2{x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28391 (x : ℝ) :
  Real.cos (2 * x) = Real.cos x ^ 2 - Real.sin x ^ 2 ∧
  Real.cos (2 * x) = 2 * Real.cos x ^ 2 - 1 ∧
  Real.cos (2 * x) = 1 - 2 * Real.sin x ^ 2   :=  by sorry
