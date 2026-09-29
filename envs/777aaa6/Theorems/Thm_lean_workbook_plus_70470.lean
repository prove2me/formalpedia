-- Prove2me | Theorems.Thm_lean_workbook_plus_70470
-- name    : lean_workbook_plus_70470
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/03b334d4-333a-4bd1-9bbe-d9dcab1d9804
-- statement:
--   Prove that \(x^7-3^7x+2.3^7\ge 0\) for \(x\ge 3\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70470  (x : ℝ)
  (h₀ : 3 ≤ x) :
  x^7 - 3^7 * x + 2 * 3^7 ≥ 0   :=  by sorry
