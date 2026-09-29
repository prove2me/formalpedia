-- Prove2me | Theorems.Thm_lean_workbook_plus_26800
-- name    : lean_workbook_plus_26800
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/e593e2e3-a161-4ca6-b325-f1c95484c66f
-- statement:
--   $f(x)=0$ $\forall x\notin\left\{\frac 32,2\right\}$ and $f(2)=f(\frac 32)=\pi$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26800 (x : ℝ) (f : ℝ → ℝ) (hf: f x = if x ≠ 3 / 2 ∧ x ≠ 2 then 0 else π): f x = if x ≠ 3 / 2 ∧ x ≠ 2 then 0 else π   :=  by sorry
