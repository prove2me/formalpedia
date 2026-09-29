-- Prove2me | Theorems.Thm_lean_workbook_plus_27568
-- name    : lean_workbook_plus_27568
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/837bb044-e3e3-445c-8cae-34718b5e5ccd
-- statement:
--   Given $f(x) = -1$ for $x < 0$ and $f(x) = 1$ for $x \geq 0$, and $g(x) = 0$ for all $x$, is $g \circ f(x)$ continuous at $x = 0$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27568 (f g : ℝ → ℝ) (hf : f = fun x => if x < 0 then -1 else 1) (hg : g = fun _ => 0) : Continuous (g ∘ f)   :=  by sorry
