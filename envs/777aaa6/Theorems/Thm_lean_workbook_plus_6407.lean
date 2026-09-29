-- Prove2me | Theorems.Thm_lean_workbook_plus_6407
-- name    : lean_workbook_plus_6407
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/4d4ad6f9-3737-45d0-8c63-f0b33c01cf43
-- statement:
--   now if $a=0$ then it is obviously true, so let $|a|>0$ then we have to show $|1+\frac{b}{a}|+2|1-\frac{b}{a}|\ge 2$ or $|1+k|+2|1-k|\ge 2, \forall k\in\mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6407 (b a : ℝ) (ha : a ≠ 0) : |1 + b / a| + 2 * |1 - b / a| ≥ 2   :=  by sorry
