-- Prove2me | Theorems.Thm_lean_workbook_plus_19665
-- name    : lean_workbook_plus_19665
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/f1022793-4197-4fc1-ab63-2b6b2cb4f62a
-- statement:
--   Suppose $f$ satisfies the $0$ -sum property. Then $0=f(x)+f(x+1/2)=f(x+1/2)+f(x+1)\implies f(x)=f(x+1)$ for all $x\in \mathbb {R}.$ Thus $f$ is periodic of period $1.$ This opens the door to Fourier series.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19665 (f : ℝ → ℝ) (hf : ∀ x, f x + f (x + 1 / 2) = 0) :
  ∀ x, f x = f (x + 1)   :=  by sorry
