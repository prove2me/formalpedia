-- Prove2me | Theorems.Thm_lean_workbook_plus_49513
-- name    : lean_workbook_plus_49513
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/b4995eda-eee6-4bed-b67a-765f585e5607
-- statement:
--   Prove that the function $f(x)$ defined by $|f(x)-f(y)|\leq\frac{1}{2}|x-y|$ for all real x,y is continuous.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49513 (f : ℝ → ℝ) (hf: ∀ x y : ℝ, abs (f x - f y) ≤ (1/2) * abs (x - y)) : Continuous f   :=  by sorry
