-- Prove2me | Theorems.Thm_lean_workbook_plus_65157
-- name    : lean_workbook_plus_65157
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/0356f475-a3ad-4fa1-b4a7-8e5ee6c5b0ac
-- statement:
--   If $a+b>0$, $b+c>0$, and $c+a>0$, then $a^2 \geq b^2$ if and only if $a \geq b$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65157 (a b : ℝ) (ha : a + b > 0) (hb : b + c > 0) (hc : a + c > 0) : a^2 ≥ b^2 ↔ a ≥ b   :=  by sorry
