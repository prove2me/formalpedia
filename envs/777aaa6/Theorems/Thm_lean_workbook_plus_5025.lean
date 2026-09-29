-- Prove2me | Theorems.Thm_lean_workbook_plus_5025
-- name    : lean_workbook_plus_5025
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/fc0a3ad5-8362-4bd1-be88-422a2f7840d8
-- statement:
--   Prove that $a/(b+c) + b/(c+a) + c/(a+b) \geq 3/2$ for all $a,b,c > 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5025 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) : a / (b + c) + b / (c + a) + c / (a + b) ≥ 3 / 2   :=  by sorry
