-- Prove2me | Theorems.Thm_lean_workbook_plus_63591
-- name    : lean_workbook_plus_63591
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/5b778d5c-5a5a-447c-832f-674048f76cc5
-- statement:
--   Let $a+b=1$. Prove that $\dfrac{1}{2}> \dfrac{a}{b+2} + \dfrac{b}{a+2}$ for all positive reals $a$ and $b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_63591 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : 1 / 2 > a / (b + 2) + b / (a + 2)   :=  by sorry
