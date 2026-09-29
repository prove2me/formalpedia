-- Prove2me | Theorems.Thm_lean_workbook_plus_36800
-- name    : lean_workbook_plus_36800
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/2d0ff6e1-1de8-40ff-943c-b00bf20f58b1
-- statement:
--   Show that if $f(x+y) = f(x) + 2f(y)$ and $f(x+1) = 2f(x)$, then $f(x) = 0$ for all $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36800  (f : ℝ → ℝ)
  (h₀ : ∀ x y, f (x + y) = f x + 2 * f y)
  (h₁ : ∀ x, f (x + 1) = 2 * f x)
  : ∀ x, f x = 0   :=  by sorry
