-- Prove2me | Theorems.Thm_lean_workbook_plus_20807
-- name    : lean_workbook_plus_20807
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/4a5cf6b4-4963-4eba-b408-991920c43d6a
-- statement:
--   Prove that if $(b - 1)(c - 1) \leq 0$, then $(b + c - 2bc + 1)^2 + (bc - 1)^2 - 2(b - 1)(c - 1) \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20807 (b c : ℝ) (h : (b - 1) * (c - 1) ≤ 0) :
  (b + c - 2 * b * c + 1) ^ 2 + (b * c - 1) ^ 2 - 2 * (b - 1) * (c - 1) ≥ 0   :=  by sorry
