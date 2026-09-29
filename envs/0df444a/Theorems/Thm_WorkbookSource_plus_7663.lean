-- Prove2me | Theorems.Thm_WorkbookSource_plus_7663
-- name    : WorkbookSource.plus_7663
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:48:11.59203+00:00
-- url     : https://prove2.me/theorems/75756569-e46d-4082-a24e-50ffb1ebfd5c
-- title:
--   A pair-product sum with a reciprocal product correction
-- statement:
--   Let $ a, b, c$ be positive real numbers satisfying $ a + b + c = 3$ . Prove that: $ ab + bc + ca + \frac {1}{abc} \ge 3 + abc$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_7663` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_7663; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_7663 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a + b + c = 3) : a * b + b * c + c * a + 1 / (a * b * c) ≥ 3 + a * b * c   :=  by sorry
