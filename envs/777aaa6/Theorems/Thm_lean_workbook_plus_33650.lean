-- Prove2me | Theorems.Thm_lean_workbook_plus_33650
-- name    : lean_workbook_plus_33650
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/8e47d8fd-5134-43f9-8a1b-0259f4b0aacd
-- statement:
--   Now we have $x+y=10$ , so $xy \leq \frac{1}{4}(x+y)^2 = 25$ . Equality occurs when $x=y=5$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33650  (x y : ℝ)
  (h₀ : x + y = 10) :
  x * y ≤ 25   :=  by sorry
