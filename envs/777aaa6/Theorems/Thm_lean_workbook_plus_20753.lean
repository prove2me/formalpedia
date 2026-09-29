-- Prove2me | Theorems.Thm_lean_workbook_plus_20753
-- name    : lean_workbook_plus_20753
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/7cb2e4dc-b637-44fe-9b01-3726b951765b
-- statement:
--   Prove that $\left(x-\frac{\pi}{4}\right)^2\geq0$ for $x\in[0,\frac{\pi}{2}]$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20753 (x : ℝ) (hx : 0 ≤ x ∧ x ≤ π / 2) :
  (x - π / 4) ^ 2 ≥ 0   :=  by sorry
