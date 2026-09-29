-- Prove2me | Theorems.Thm_lean_workbook_plus_74766
-- name    : lean_workbook_plus_74766
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/0cea6278-c618-42bd-a840-70ad1b84937f
-- statement:
--   Applying AM-GM, we get \n $4\left( {{b^2} + bc + {c^2}} \right)\left( {ab + bc + ca} \right) \le {\left( {ab + bc + ca + {b^2} + bc + {c^2}} \right)^2} = {(b + c)^2}{(a + b + c)^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74766  (a b c : ℝ) :
  4 * (b^2 + b * c + c^2) * (a * b + b * c + c * a) ≤ (a * b + b * c + c * a + b^2 + b * c + c^2)^2   :=  by sorry
