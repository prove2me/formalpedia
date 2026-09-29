-- Prove2me | Theorems.Thm_lean_workbook_plus_81133
-- name    : lean_workbook_plus_81133
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/c9fae72c-e109-41ce-b7e1-9f3a2bd284d9
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{R}$ be a function such that $f\left ( \frac{x+y}{3} \right )=\frac{f(x)+f(y)}{2}$ . Prove that the function $g:\mathbb{R}\to\mathbb{R}$ , $g(x)=f(x)-f(0)$ is additive.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81133 (f : ℝ → ℝ) (hf : ∀ x y, f ((x + y) / 3) = (f x + f y) / 2) :
    ∀ x y, f (x + y) - f 0 = f x - f 0 + (f y - f 0)   :=  by sorry
