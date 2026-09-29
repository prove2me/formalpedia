-- Prove2me | Theorems.Thm_lean_workbook_plus_61970
-- name    : lean_workbook_plus_61970
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/df81a026-4093-40f2-91a4-50e19e5ffadc
-- statement:
--   For $0<x\le1,\ \frac{x}{x+1}\ge\frac{x}{2}.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61970 : ∀ x : ℝ, 0 < x ∧ x ≤ 1 → x / (x + 1) ≥ x / 2   :=  by sorry
