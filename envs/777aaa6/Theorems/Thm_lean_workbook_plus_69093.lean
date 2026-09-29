-- Prove2me | Theorems.Thm_lean_workbook_plus_69093
-- name    : lean_workbook_plus_69093
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/fe013e46-be84-4bc5-baff-a2431b91291b
-- statement:
--   $10^n\equiv0\pmod4$ for $n>1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69093 (n : ℕ) (h : n > 1) : 10^n ≡ 0 [ZMOD 4]   :=  by sorry
