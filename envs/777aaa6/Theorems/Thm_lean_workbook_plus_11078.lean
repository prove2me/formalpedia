-- Prove2me | Theorems.Thm_lean_workbook_plus_11078
-- name    : lean_workbook_plus_11078
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/999bf7a7-6eb8-42b7-9904-577525b646ec
-- statement:
--   Find a particular solution for $T'' -\frac{2}{t} \cdot T' +T =0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11078 (t : ℝ) (ht : t > 0) : ∃ T, T'' - (2/t) * T' + T = 0   :=  by sorry
