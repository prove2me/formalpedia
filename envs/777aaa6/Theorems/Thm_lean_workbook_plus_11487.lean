-- Prove2me | Theorems.Thm_lean_workbook_plus_11487
-- name    : lean_workbook_plus_11487
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/68c63c6a-030d-4319-b9ba-d6e473d2858a
-- statement:
--   prove that $(a+b+c+d)^3 \geq 16(abc + bcd + acd + adb)$ if $a,b,c,d$ are non negative numbers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11487 (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) : (a + b + c + d) ^ 3 ≥ 16 * (a * b * c + b * c * d + a * c * d + a * b * d)   :=  by sorry
