-- Prove2me | Theorems.Thm_lean_workbook_plus_54388
-- name    : lean_workbook_plus_54388
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/35ed8dde-52fa-47d5-8ea6-08af291a8d5b
-- statement:
--   Suppose that $f(x)$ and $g(x)$ are positive for all $x$ . If $f(x)$ and $g(x)$ are both monotonically increasing, then must $f(x)\cdot g(x)$ be monotonically increasing?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54388  (f g : ℝ → ℝ)
  (hf : ∀ x, 0 < f x)
  (hg : ∀ x, 0 < g x)
  (hf' : ∀ x y, x ≤ y → f x ≤ f y)
  (hg' : ∀ x y, x ≤ y → g x ≤ g y)
  : ∀ x y, x ≤ y → f x * g x ≤ f y * g y   :=  by sorry
