-- Prove2me | Theorems.Thm_lean_workbook_plus_46553
-- name    : lean_workbook_plus_46553
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/ff28bc91-bed4-4604-afb7-e3ae63ed8643
-- statement:
--   Let $a,b,c$ , be positive real numbers such that $a+b+c\le\frac{3}{2}$ . Prove or disprove: \n $a+b+c+\frac{1}{a}+\frac{1}{b}+\frac{1}{c}\ge\frac{15}{2} .$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_46553 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)(habc : a * b * c = 1) (hab : a + b + c ≤ 3 / 2) : a + b + c + 1 / a + 1 / b + 1 / c ≥ 15 / 2   :=  by sorry
