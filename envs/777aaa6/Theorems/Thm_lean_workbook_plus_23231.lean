-- Prove2me | Theorems.Thm_lean_workbook_plus_23231
-- name    : lean_workbook_plus_23231
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/c0d74513-a3bf-44db-a142-3dd8416690c8
-- statement:
--   Let $a,b>0$. Prove that $\frac{a^2}{b^2}+\frac{b}{a+b}>\frac{4}{5}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23231 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : a^2 / b^2 + b / (a + b) > 4 / 5   :=  by sorry
