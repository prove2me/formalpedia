-- Prove2me | Theorems.Thm_lean_workbook_plus_53900
-- name    : lean_workbook_plus_53900
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/8f3cf6ec-50bd-4c81-9b6e-5168bc9448db
-- statement:
--   $\ge (20^2 + 1) + (19^2 + 1) + ... + (11^2 + 1) = 2495$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53900 : ∑ k in Finset.Icc 11 20, ((k:ℕ)^2 + 1) = 2495   :=  by sorry
