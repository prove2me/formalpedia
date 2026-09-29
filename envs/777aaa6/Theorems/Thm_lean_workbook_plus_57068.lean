-- Prove2me | Theorems.Thm_lean_workbook_plus_57068
-- name    : lean_workbook_plus_57068
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/6de4a15c-6f2c-4c10-ac00-ebf7486095c8
-- statement:
--   Prove that $(x+y+z)(xab+ybc+zca)\leq(x^2+y^2+z^2)(a^2+b^2+c^2)$ For all reals a,b,c,x,y,z. Can it be proved by Cauchy or Holder?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57068 (x y z a b c : ℝ) : (x + y + z) * (x * a * b + y * b * c + z * c * a) ≤ (x ^ 2 + y ^ 2 + z ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2)   :=  by sorry
