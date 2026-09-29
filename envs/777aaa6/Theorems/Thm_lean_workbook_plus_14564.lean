-- Prove2me | Theorems.Thm_lean_workbook_plus_14564
-- name    : lean_workbook_plus_14564
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/c9cd8e51-266e-4cce-912c-2127109b3bd2
-- statement:
--   Suppose that for an integer $n>9$ we have ${2^n}>{n^3},$ we want to prove that $2^{n+1} > (n+1)^3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14564 (n : ℕ) (hn : 9 < n) (h : 2^n > n^3) : 2^(n + 1) > (n + 1)^3   :=  by sorry
