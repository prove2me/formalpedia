-- Prove2me | Theorems.Thm_lean_workbook_plus_39408
-- name    : lean_workbook_plus_39408
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/5f037b2b-e7ce-48e9-bfbe-dbb1c6cd287e
-- statement:
--   Prove that for any real numbers $x$ and $y$, there exist integers $a$ and $b$ (not both zero) such that $|a\sin(x) - b\cos(y)| < \frac{1}{9}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39408 (x y : ℝ) : ∃ a b : ℤ, a ≠ 0 ∨ b ≠ 0 ∧ |a * Real.sin x - b * Real.cos y| < 1 / 9   :=  by sorry
