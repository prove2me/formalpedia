-- Prove2me | Theorems.Thm_lean_workbook_plus_21617
-- name    : lean_workbook_plus_21617
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/60ed992d-9306-43fe-96a8-3bf2a859bb68
-- statement:
--   Determine if the Intermediate Value Theorem (IVT) conclusion holds for the function $f(x) = \sin(\frac{\pi}{x})$ when $x \neq 0$ and $f(x) = 0$ when $x = 0$, with domain [-2, 2].
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21617 (f : ℝ → ℝ) (hf: f = fun x => if x = 0 then 0 else sin (π / x)) : ∀ x y : ℝ, x < y → f x < f y ∨ f x = f y ∨ f x > f y   :=  by sorry
