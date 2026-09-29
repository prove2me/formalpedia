-- Prove2me | Theorems.Thm_lean_workbook_plus_10229
-- name    : lean_workbook_plus_10229
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/56cbdbb8-530c-43b5-9103-9e0509166f75
-- statement:
--   Prove: $4(a^2 + b^2 + c^2 + d^2 + e^2) \geq 2(ab + ac + bc + bd + cd + ce + de + da + ea + eb)$ for $a,b,c,d,e>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10229 (a b c d e : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (he : 0 < e) : 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2) ≥ 2 * (a * b + a * c + b * c + b * d + c * d + c * e + d * e + d * a + e * a + e * b)   :=  by sorry
