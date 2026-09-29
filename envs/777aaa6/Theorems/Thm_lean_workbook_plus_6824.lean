-- Prove2me | Theorems.Thm_lean_workbook_plus_6824
-- name    : lean_workbook_plus_6824
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/a82bf4a7-4457-4e71-8106-aa61290d3fce
-- statement:
--   Prove that for four positive real numbers $a,b,c,d$ the following inequality holds and find all equality cases: \n $$a^3 +b^3 +c^3 +d^3 \geq a^2 b +b^2 c+ c^2 d +d^2 a.$$ \n\nAM-GM is nicer and there should also be some factorization, but Muirhead with $[3,0,0]\succeq [2,1,0]$ kills it.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6824 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) : a^3 + b^3 + c^3 + d^3 ≥ a^2 * b + b^2 * c + c^2 * d + d^2 * a   :=  by sorry
