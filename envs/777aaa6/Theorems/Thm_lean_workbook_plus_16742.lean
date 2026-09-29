-- Prove2me | Theorems.Thm_lean_workbook_plus_16742
-- name    : lean_workbook_plus_16742
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/cdb35369-d2e2-47bb-9062-8d2b2c9daa47
-- statement:
--   as $ a,k$ are integers, $ (a-2+k)$ , $ (a-2-k)$ have the same parity.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16742 (a k : ℤ) : (a - 2 + k) % 2 = (a - 2 - k) % 2   :=  by sorry
