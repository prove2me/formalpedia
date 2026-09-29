-- Prove2me | Theorems.Thm_lean_workbook_plus_58081
-- name    : lean_workbook_plus_58081
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/2755aa7c-6a77-4da2-8dc0-f60d9f28cb0e
-- statement:
--   Find continuous $f:\mathbb{R}\longrightarrow\mathbb{R},$ with $\forall x,y,z, \; f(\frac {x+2y}3)+f(\frac {y+2z}3)+f(\frac {z+2x}3)=f(x)+f(y)+ f(z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58081 : ∃ f : ℝ → ℝ, Continuous f ∧ ∀ x y z : ℝ, f ((x + 2 * y) / 3) + f ((y + 2 * z) / 3) + f ((z + 2 * x) / 3) = f x + f y + f z   :=  by sorry
