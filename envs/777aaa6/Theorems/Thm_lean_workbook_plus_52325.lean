-- Prove2me | Theorems.Thm_lean_workbook_plus_52325
-- name    : lean_workbook_plus_52325
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/26bd7449-f7eb-4639-85e2-7db208beeff2
-- statement:
--   Verify the property of cardinal arithmetic: $2^{\aleph_0}=\left(2^{\aleph_0}\right)^{\aleph_0}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52325 (ha : 2 ≤ ℵ₀) : 2 ^ ℵ₀ = (2 ^ ℵ₀) ^ ℵ₀   :=  by sorry
