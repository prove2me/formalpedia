-- Prove2me | Theorems.Thm_lean_workbook_plus_21180
-- name    : lean_workbook_plus_21180
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/2553d8ba-73b8-4fed-9ce8-0b5bd1729766
-- statement:
--   When $x, y \in \mathbb{R}$, then $f(2xy) = f(x) + f(y)$. In addition, $f(2) = 7$. Find $f(1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21180 (f : ℝ → ℝ) (hf : ∀ x y, f (2 * x * y) = f x + f y) : f 2 = 7 → f 1 = 7   :=  by sorry
