-- Prove2me | Theorems.Thm_lean_workbook_plus_24066
-- name    : lean_workbook_plus_24066
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/89d29e54-e8db-4e60-9fbb-576567c267da
-- statement:
--   Prove that $(xy + yz + xz - 1)^2 \leq (1 + x^2)(1 + y^2)(1 + z^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24066 (x y z : ℝ) : (x * y + y * z + x * z - 1) ^ 2 ≤ (1 + x ^ 2) * (1 + y ^ 2) * (1 + z ^ 2)   :=  by sorry
