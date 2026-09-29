-- Prove2me | Theorems.Thm_lean_workbook_plus_76254
-- name    : lean_workbook_plus_76254
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/e13ec9f1-4222-4071-b840-f45ab83a4d82
-- statement:
--   prove that $ k+1\le 2^{k} $ for all $ k\ge 1 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76254 (k : ℕ) (h : 1 ≤ k) : k + 1 ≤ 2 ^ k   :=  by sorry
