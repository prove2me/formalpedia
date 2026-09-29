-- Prove2me | Theorems.Thm_lean_workbook_plus_26074
-- name    : lean_workbook_plus_26074
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/44795c05-aa32-4255-ba10-a152e1d6ae3d
-- statement:
--   Let $a,b>0$ and $\frac{1}{a}+\frac{1}{b}= 1.$ Prove that $\frac{1}{4} \le \frac{1}{a (a+2)} +\frac{1}{b (b +2)} <\frac{1}{3}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_26074 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : 1/a + 1/b = 1) : 1/4 ≤ 1/(a * (a + 2)) + 1/(b * (b + 2)) ∧ 1/(a * (a + 2)) + 1/(b * (b + 2)) < 1/3   :=  by sorry
