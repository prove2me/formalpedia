-- Prove2me | Theorems.Thm_lean_workbook_plus_75525
-- name    : lean_workbook_plus_75525
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/d999a163-fe14-4f6a-b1cf-57612680a883
-- statement:
--   which is true as $2=|1+k+1-k|\le |1+k|+|1-k|\le |1+k|+2|1-k|, \forall k\in \mathbb{R}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75525 (k : ℝ) : 2 ≤ abs (1 + k) + 2 * abs (1 - k)   :=  by sorry
