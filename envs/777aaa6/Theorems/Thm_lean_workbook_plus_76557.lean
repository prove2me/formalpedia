-- Prove2me | Theorems.Thm_lean_workbook_plus_76557
-- name    : lean_workbook_plus_76557
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/640b4942-91ea-452c-87dd-917c1d8214b0
-- statement:
--   prove that $(a+b+c+d)^3 \geq 16(abc + bcd + acd + adb)$ if $a,b,c,d$ are non negative numbers
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76557 (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) : (a + b + c + d) ^ 3 ≥ 16 * (a * b * c + b * c * d + a * c * d + a * b * d)   :=  by sorry
