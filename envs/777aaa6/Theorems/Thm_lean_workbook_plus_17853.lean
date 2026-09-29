-- Prove2me | Theorems.Thm_lean_workbook_plus_17853
-- name    : lean_workbook_plus_17853
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/7e3dce9a-da4f-45e1-a2f0-3f001ae41de7
-- statement:
--   Prove that $2(a+b+c)-abc\le 10$ given $a,b,c\in \Bbb{R^*_+}$ with $a^2+b^2+c^2=9$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17853 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) (h : a^2 + b^2 + c^2 = 9) : 2 * (a + b + c) - a * b * c ≤ 10   :=  by sorry
