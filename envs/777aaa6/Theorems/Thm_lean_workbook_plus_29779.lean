-- Prove2me | Theorems.Thm_lean_workbook_plus_29779
-- name    : lean_workbook_plus_29779
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/b7abada1-bdb1-49a7-aa4d-e5bacb056aef
-- statement:
--   Let $ a,b,c>0 $ and $a^2 +b^2+c^2 =1$ . Prove that \n $\frac{1}{1-ab}+\frac{1}{1-bc}+\frac{1}{1-ca}\leq\frac{9}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_29779 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : 1 / (1 - a * b) + 1 / (1 - b * c) + 1 / (1 - c * a) ≤ 9 / 2   :=  by sorry
