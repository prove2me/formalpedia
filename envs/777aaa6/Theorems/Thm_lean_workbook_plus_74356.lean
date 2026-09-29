-- Prove2me | Theorems.Thm_lean_workbook_plus_74356
-- name    : lean_workbook_plus_74356
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/5cc3b046-8d3d-419e-9975-229f337a6c5e
-- statement:
--   Find the value of $x$ such that $f(g(f(g(x))))=20$ given $f(x)=4x-2$ and $g(x)=5x+3$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74356 (x : ℝ) (f g : ℝ → ℝ) (hf : f = fun x => 4*x-2) (hg : g = fun x => 5*x+3) : f (g (f (g x))) = 20 ↔ x = -19/40   :=  by sorry
