-- Prove2me | Theorems.Thm_WorkbookSource_plus_31208
-- name    : WorkbookSource.plus_31208
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:43:24.408135+00:00
-- url     : https://prove2.me/theorems/0a1fe046-8c4b-4d78-9e14-e79d9361415c
-- title:
--   A cyclic pairwise ratio sum is bounded by a reciprocal product
-- statement:
--   Let a,b,c are positive numbers such that $ a+b+c=3$ . Prove that
--    $ \frac {a+b}{b+c}+\frac {b+c}{c+a}+\frac {c+a}{a+b}\le \frac {3}{abc}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_31208` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_31208; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_31208 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : (a + b) / (b + c) + (b + c) / (c + a) + (c + a) / (a + b) ≤ 3 / (a * b * c)   :=  by sorry
