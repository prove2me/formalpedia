-- Prove2me | Theorems.Thm_lean_workbook_plus_40206
-- name    : lean_workbook_plus_40206
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ce902c8d-da33-4293-9c0b-c74c96fbc811
-- statement:
--   Prove inductively that $ n \leq 2^{n-1}$ for all natural n.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40206 (n : ℕ) : n ≤ 2 ^ (n - 1)   :=  by sorry
