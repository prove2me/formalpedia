-- Prove2me | Theorems.Thm_lean_workbook_plus_67976
-- name    : lean_workbook_plus_67976
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/ddff8b2d-31a7-4b76-aa23-cdfc1290ca6a
-- statement:
--   For odd $n$, prove that $8\mid(n^2-1)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67976 (n : ℤ) (h : n%2 = 1) : 8 ∣ (n^2 - 1)   :=  by sorry
