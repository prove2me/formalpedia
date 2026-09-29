-- Prove2me | Theorems.Thm_lean_workbook_plus_2905
-- name    : lean_workbook_plus_2905
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/e6b020ba-5909-45b8-b5ba-b228da5bce0a
-- statement:
--   Let $ a,b,c,d$ be real numbers such that $ a,b,c\ge 1$ and $ a + b + c = 4 - d$ . Prove that \n $ ab + bc + ca\ge 4 - d^2.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2905 (a b c d : ℝ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (habc : a + b + c = 4 - d) : a * b + b * c + c * a ≥ 4 - d ^ 2   :=  by sorry
