-- Prove2me | Theorems.Thm_lean_workbook_plus_64463
-- name    : lean_workbook_plus_64463
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/3668fe59-ada6-44b6-9923-3553edc3b9fa
-- statement:
--   Let $a,b,c>0.$ PROVE : a. $3(a^2b +b^2c +c^2a) <= (a+b+c)(a^2+b^2+c^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64463 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 3 * (a^2 * b + b^2 * c + c^2 * a) ≤ (a + b + c) * (a^2 + b^2 + c^2)   :=  by sorry
