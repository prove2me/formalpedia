-- Prove2me | Theorems.Thm_lean_workbook_plus_34483
-- name    : lean_workbook_plus_34483
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/69904e82-0685-404e-825d-c04ee067fc3e
-- statement:
--   Given $f(x) = -1$ for $x < 0$ and $f(x) = 1$ for $x \geq 0$, and $g(x) = 0$ for all $x$, is $g \circ f(x)$ continuous at $x = 0$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34483 (f g : ℝ → ℝ) (hf : ∀ x, f x = if x < 0 then -1 else 1) (hg : ∀ x, g x = 0) : Continuous (g ∘ f)   :=  by sorry
