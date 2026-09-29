-- Prove2me | Theorems.Thm_lean_workbook_plus_77333
-- name    : lean_workbook_plus_77333
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/1a3c3115-9977-4de0-85bc-fd7312769ffb
-- statement:
--   Prove that $\frac{|x|}{(1+x^2)(1+y^2)} \leq \frac{1}{2}$ for all $x, y \in \mathbb{R}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77333 : ∀ x y : ℝ, |x| / ((1 + x ^ 2) * (1 + y ^ 2)) ≤ 1 / 2   :=  by sorry
