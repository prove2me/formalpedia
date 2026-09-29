-- Prove2me | Theorems.Thm_lean_workbook_plus_147
-- name    : lean_workbook_plus_147
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/173d1bcd-a014-4db4-a4e0-f26e409b6801
-- statement:
--   If the next relation holds for every real numbers x,y : $f(x+y)=f(x-y)$ then we can conclude that f is constant?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_147 (f : ℝ → ℝ) (hf: ∀ x y : ℝ, f (x + y) = f (x - y)) : ∃ a :ℝ, ∀ x : ℝ, f x = a   :=  by sorry
