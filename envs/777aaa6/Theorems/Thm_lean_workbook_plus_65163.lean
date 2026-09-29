-- Prove2me | Theorems.Thm_lean_workbook_plus_65163
-- name    : lean_workbook_plus_65163
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/4d8535fa-1dad-492d-8f96-bd17f1577ba5
-- statement:
--   Solve for x: $x^{2}=a+b$, where $a$ is the floor function of $x^{2}$ and $b$ is its fractional part
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65163 (x : ℝ) (a b : ℝ) (ha : a = ⌊x^2⌋) (hb : b = x^2 - ⌊x^2⌋) : a + b = x^2   :=  by sorry
