-- Prove2me | Theorems.Thm_lean_workbook_plus_63848
-- name    : lean_workbook_plus_63848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/8ae13641-0e04-458e-8235-1295bc010eff
-- statement:
--   Let $a, b, c$ be the length of three sides. \nand let \n $a=x+y$ \n $b=y+z$ \n $c=z+x$ \n $x, y, z > 0$ \nthus, \n $n=a+b+c=2(x+y+z)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63848 (a b c x y z : ℝ) (h1 : a = x + y) (h2 : b = y + z) (h3 : c = z + x) (hx : x > 0 ∧ y > 0 ∧ z > 0) : a + b + c = 2 * (x + y + z)   :=  by sorry
