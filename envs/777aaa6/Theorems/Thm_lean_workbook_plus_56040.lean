-- Prove2me | Theorems.Thm_lean_workbook_plus_56040
-- name    : lean_workbook_plus_56040
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/0bd877de-02e6-48c5-bba4-1c2cb2253f8f
-- statement:
--   Prove that if $y \geq 0$ and $y(y+1) \leq (x+1)^2$ then $y(y-1) \leq x^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56040 {x y : ℝ} (h : y ≥ 0) (h' : y * (y + 1) ≤ (x + 1) ^ 2) : y * (y - 1) ≤ x ^ 2   :=  by sorry
