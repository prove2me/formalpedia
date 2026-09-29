-- Prove2me | Theorems.Thm_lean_workbook_plus_73481
-- name    : lean_workbook_plus_73481
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/96a6ab40-6d41-4ac7-9897-db6a10a47310
-- statement:
--   Prove that if $a$ and $b$ are two consecutive integers, then $gcd(a, b) = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_73481 (a b : ℤ) (h : a + 1 = b) : gcd a b = 1   :=  by sorry
