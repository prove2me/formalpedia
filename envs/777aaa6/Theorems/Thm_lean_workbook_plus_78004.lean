-- Prove2me | Theorems.Thm_lean_workbook_plus_78004
-- name    : lean_workbook_plus_78004
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/03b4be7b-ccb3-4b6b-8bb1-ccb52b6b9ff1
-- statement:
--   prove that \n\n $\frac{b^2}{c}+c\ge 2b$ \n\n given $b,c>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78004 (b c : ℝ) (hb : b > 0) (hc : c > 0) : (b^2 / c + c) ≥ 2 * b   :=  by sorry
