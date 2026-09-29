-- Prove2me | Theorems.Thm_lean_workbook_plus_11032
-- name    : lean_workbook_plus_11032
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/1a307c32-ce03-419c-bb72-2ed8bb290f6d
-- statement:
--   If $a,b,c$ are reals positives. Prove that \n $$\frac{a^2}{b^2+2c^2}+\frac{b^2}{c^2+2a^2}+\frac{c^2}{a^2+2b^2}\ge 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11032 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : (a^2 / (b^2 + 2 * c^2) + b^2 / (c^2 + 2 * a^2) + c^2 / (a^2 + 2 * b^2)) ≥ 1   :=  by sorry
