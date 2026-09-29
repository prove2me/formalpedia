-- Prove2me | Theorems.Thm_lean_workbook_plus_31047
-- name    : lean_workbook_plus_31047
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/de6025ac-da7a-4098-8217-1d025a265d81
-- statement:
--   The derivative is $f'(x)=1+2x+3x^2+\dots+100x^{99}$ , whence $f'(1)=1+2+3+\dots+100=\frac{100\cdot101}{2}=\boxed{5050}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_31047  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x = ∑ k in (Finset.range 100), (k + 1) * x^k) :
  f 1 = 5050   :=  by sorry
