-- Prove2me | Theorems.Thm_lean_workbook_plus_40344
-- name    : lean_workbook_plus_40344
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/6e6e15d1-fc12-4af3-8562-10f4af0111c6
-- statement:
--   Let $a,b,c$ be real numbers such that $a+b+c=0$ and $|a|+|b|+|c|=1$. Prove that $a+\frac{b}{2}+\frac{c}{3}\le \frac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40344 (a b c : ℝ) (hab : a + b + c = 0) (hbc : abs a + abs b + abs c = 1) :
  a + b / 2 + c / 3 ≤ 1 / 3   :=  by sorry
