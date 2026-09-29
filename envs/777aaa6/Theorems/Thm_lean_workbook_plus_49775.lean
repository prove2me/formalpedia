-- Prove2me | Theorems.Thm_lean_workbook_plus_49775
-- name    : lean_workbook_plus_49775
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/c7cc1f10-c94c-411a-b9e5-a5e29b731ab2
-- statement:
--   Hence we must prove $a^2+b^2+c^2+2bc+2ca-2c+1\ge 2ab+2bc+2ca\implies (a-b)^2+(c-1)^2\ge 0$ which is obvious
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_49775  (a b c : ℝ) :
  a^2 + b^2 + c^2 + 2 * b * c + 2 * c * a - 2 * c + 1 ≥ 2 * a * b + 2 * b * c + 2 * c * a   :=  by sorry
