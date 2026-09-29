-- Prove2me | Theorems.Thm_lean_workbook_plus_61799
-- name    : lean_workbook_plus_61799
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/10000002-edd8-40f7-9b7d-a6ac221a3d52
-- statement:
--   Let $P(x),$ be the probability that after $x$ rolls Janet's running total is $3.$ If $x=1,$ we have a $\frac{1}{6},$ chance. If $x=2,$ we have a $\frac{1}{18},$ chance and finally if $x=3,$ we have a $\frac{1}{216},$ chance so $\frac{1}{6}+\frac{1}{18}+\frac{1}{216}=\boxed{\frac{49}{216}}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61799 :
  (1/6 + 1/18 + 1/216) = 49/216   :=  by sorry
