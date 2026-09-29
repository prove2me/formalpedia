-- Prove2me | Theorems.Thm_lean_workbook_plus_24983
-- name    : lean_workbook_plus_24983
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1b1daea1-6221-4612-9839-262fd198b336
-- statement:
--   Show that the function $f(x) = e^x \cos x$ takes the value 1 infinitely many times, and find the intervals where it has exactly two solutions.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24983 (f : ℝ → ℝ) (hf: f = fun x => (Real.exp x) * (Real.cos x)) : ∃ x, f x = 1 ∧ ∀ y, y < x → f y ≠ 1   :=  by sorry
