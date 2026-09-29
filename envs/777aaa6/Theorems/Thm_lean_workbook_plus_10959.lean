-- Prove2me | Theorems.Thm_lean_workbook_plus_10959
-- name    : lean_workbook_plus_10959
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/bdd4f234-1838-4c6c-8022-26ede4206068
-- statement:
--   Let $a,b,c$ be real numbers such that $a+b+c=0$ and $ |a|+|b|+|c|=1$ . Prove that $$a+\frac{b}{2}+\frac{c}{3}\leq\frac{1}{3}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10959 (a b c : ℝ) (h1 : a + b + c = 0) (h2 : abs a + abs b + abs c = 1) :
  a + b / 2 + c / 3 ≤ 1 / 3   :=  by sorry
