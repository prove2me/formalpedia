-- Prove2me | Theorems.Thm_lean_workbook_plus_26729
-- name    : lean_workbook_plus_26729
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/1fe8e875-65b7-4827-900b-b8898e6915b2
-- statement:
--   Let $a,b>0$ and $a+b=1.$ Prove that \n $$\frac{2+a}{2-a}+\frac{2+b}{2 -b}\geq \frac{10}{3}$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26729 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) : (2 + a) / (2 - a) + (2 + b) / (2 - b) ≥ 10 / 3   :=  by sorry
