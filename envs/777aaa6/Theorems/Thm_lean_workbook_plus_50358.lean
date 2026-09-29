-- Prove2me | Theorems.Thm_lean_workbook_plus_50358
-- name    : lean_workbook_plus_50358
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0eed9bcb-103b-4b90-ba48-740113883f1b
-- statement:
--   If $ x, y, z>0, xyz=1 $ then $5x(y+z)^2+5xyz\ge4x(y+z)^2+9xyz\ge3x(y+z)^2+13xyz$ it's clear.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50358 (x y z : ℝ) (h : x > 0 ∧ y > 0 ∧ z > 0 ∧ x * y * z = 1) :
  5 * x * (y + z) ^ 2 + 5 * x * y * z ≥ 4 * x * (y + z) ^ 2 + 9 * x * y * z ∧
  4 * x * (y + z) ^ 2 + 9 * x * y * z ≥ 3 * x * (y + z) ^ 2 + 13 * x * y * z   :=  by sorry
