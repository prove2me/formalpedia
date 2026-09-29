-- Prove2me | Theorems.Thm_lean_workbook_plus_62898
-- name    : lean_workbook_plus_62898
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/78a62ae3-c08f-4bb1-a1ce-29c33bdbec66
-- statement:
--   $x \left(\frac{1}{y} + \frac{1}{z} \right) \ge \frac{4x}{y+z}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62898 (x y z : ℝ) (h : 0 < x ∧ 0 < y ∧ 0 < z) :
  x * (1/y + 1/z) ≥ 4*x/(y+z)   :=  by sorry
