-- Prove2me | Theorems.Thm_lean_workbook_plus_44988
-- name    : lean_workbook_plus_44988
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/030bafca-469b-462a-8204-e70ab6327f1e
-- statement:
--   Suppose $\lim_{x\to0}f(x)=0$. Prove that 1) $\lim_{x\to0}(f(x)+f(2x))=0$, 2) $\lim_{x\to0}(f(x)+f(x^2))=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44988 (f : ℝ → ℝ) (h : ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x| < ε) : ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x + f (2 * x)| < ε   :=  by sorry
