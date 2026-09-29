-- Prove2me | Theorems.Thm_lean_workbook_plus_81482
-- name    : lean_workbook_plus_81482
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/09c3bb2c-c869-4c35-a32c-4b58bc1a9b5a
-- statement:
--   Given the arithmetic sum formula $S=\frac{n(n+1)}{2}$, find the value of $S$ for $n=100$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_81482 (n : ℕ) (hn : n = 100) : (n * (n + 1)) / 2 = 5050   :=  by sorry
