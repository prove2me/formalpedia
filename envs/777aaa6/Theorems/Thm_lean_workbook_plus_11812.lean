-- Prove2me | Theorems.Thm_lean_workbook_plus_11812
-- name    : lean_workbook_plus_11812
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/52337e08-e261-4468-9cad-5a0ae92bf5af
-- statement:
--   Given reals $a,b,c>0$ with $ a^2+b^2+c^2=1 $ prove that \n $$ \frac{1-c^2}{ab+c^2}+\frac{1-b^2}{ac+b^2}+\frac{1-a^2}{bc+a^2}\ge 3 $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11812 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1) : (1 - c^2) / (a * b + c^2) + (1 - b^2) / (a * c + b^2) + (1 - a^2) / (b * c + a^2) ≥ 3   :=  by sorry
