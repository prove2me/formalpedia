-- Prove2me | Theorems.Thm_lean_workbook_plus_52954
-- name    : lean_workbook_plus_52954
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/204e4e9f-afa4-4cd5-8223-04c23f8039a6
-- statement:
--   We have $\text{gcd}(x,y)^2 | x^2,y^2 \Rightarrow \text{gcd}(x,y)^2 | x^2+y^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52954 (x y : ℤ) : (gcd x y)^2 ∣ x^2 + y^2   :=  by sorry
