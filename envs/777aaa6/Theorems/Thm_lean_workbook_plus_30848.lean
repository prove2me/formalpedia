-- Prove2me | Theorems.Thm_lean_workbook_plus_30848
-- name    : lean_workbook_plus_30848
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/b4ac77ef-c5d2-4446-80c8-74d60e7a215f
-- statement:
--   If $a,b,c>0 $ and $a^2+b^2+c^2=1$ then prove that , $ \frac{ab}{c}+\frac{bc}{a}+\frac{ca}{b} \ge \sqrt 3 $ Germany 2019
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30848 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : a * b / c + b * c / a + c * a / b ≥ Real.sqrt 3   :=  by sorry
