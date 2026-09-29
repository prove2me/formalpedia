-- Prove2me | Theorems.Thm_lean_workbook_plus_45165
-- name    : lean_workbook_plus_45165
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/83123ad1-7f91-4e60-b7f8-d2efaf420082
-- statement:
--   Let be $ a,b,c>0$ . Show that : \n\n $ (a + b + c)\bigg( \frac {1}{a} + \frac {1}{b} + \frac {1}{c}\bigg)\geq 9 + \frac {2((a-b)^2+(b-c)^2+(c-a)^2)}{ab + bc + ca}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_45165 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b + c) * (1 / a + 1 / b + 1 / c) ≥ 9 + 2 * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) / (a * b + b * c + c * a)   :=  by sorry
