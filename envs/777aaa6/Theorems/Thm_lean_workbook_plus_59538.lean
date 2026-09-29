-- Prove2me | Theorems.Thm_lean_workbook_plus_59538
-- name    : lean_workbook_plus_59538
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/51155ec1-3dda-4c5e-84ce-cf516efd856c
-- statement:
--   We have $v_2(3^{101}+5^{101})=v_2(3+5)+v_2(101)=3+0=\boxed{3}.$ If you don't know LTE: \nWe have $3^{101}+5^{101}=(3+5)(3^{100}-3^{99}5+\cdots+3^{50}5^{50}-\cdots-5^{99}3+5^{100}).$ The second term has an odd number of odd terms( $101$ ), so it is odd. The only factors of $2$ are in $3+5=8\implies\boxed{3}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59538 :
  padicValNat 2 (3^101 + 5^101) = 3   :=  by sorry
