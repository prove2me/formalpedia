-- Prove2me | Theorems.Thm_lean_workbook_plus_28663
-- name    : lean_workbook_plus_28663
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/d85eded5-87a6-4ed2-a272-b2607cf02f73
-- statement:
--   Use the fact that $1^3 + 2^3 + 3^3 + \ldots + n^3 = (1 + 2 + 3 + \ldots + n)^2$ . To get that the sum of the first 20 perfect cubes is $\frac{20(20+1)}{2}^2 = 210^2 = (200 + 10)^2 = 200^2 + 10^2 + 2(200)(10) = 40000 + 100 + 4000 = \boxed{\text{(D) } 44100}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28663 :
  ∑ k in (Finset.range 20), (k + 1)^3 = 44100   :=  by sorry
