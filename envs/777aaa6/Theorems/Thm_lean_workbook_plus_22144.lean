-- Prove2me | Theorems.Thm_lean_workbook_plus_22144
-- name    : lean_workbook_plus_22144
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/e93f5bb5-980c-4d44-ac8b-84bb27753989
-- statement:
--   Prove that $f(0)=0$ if $f$ satisfies $f(f(x)^2+f(y))=xf(x)+y$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22144 (f : ℝ → ℝ) (hf : ∀ x y, f (f x ^ 2 + f y) = x * f x + y) : f 0 = 0   :=  by sorry
