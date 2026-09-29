-- Prove2me | Theorems.Thm_lean_workbook_plus_8485
-- name    : lean_workbook_plus_8485
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/e7f72d23-ee72-4d06-934b-8fbf1ccbd4f6
-- statement:
--   Let a,b,c be positive reals such that ${a^2} + {b^2} + {c^2} + \frac{3}{2}abc = \frac{9}{2}$\nProve that : $ a+b+c \le 3 $ \nHave fun
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8485 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 + (3 / 2) * a * b * c = 9 / 2) : a + b + c ≤ 3   :=  by sorry
