-- Prove2me | Theorems.Thm_lean_workbook_plus_48583
-- name    : lean_workbook_plus_48583
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b6886deb-d485-4705-bcff-cbddd652062d
-- statement:
--   Prove that if $\lim_{x \to 0}f(x)=L$ then $\lim_{x \to 0}f(cx)=L$ for any nonzero constant c.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48583 (c : ℝ) (f : ℝ → ℝ) (L : ℝ) (h : c ≠ 0) : (∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f x - L| < ε) → ∀ ε > 0, ∃ δ > 0, ∀ x, |x| < δ → |f (c * x) - L| < ε   :=  by sorry
