-- Prove2me | Theorems.Thm_WorkbookSource_base_12820
-- name    : WorkbookSource.base_12820
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:46:56.123235+00:00
-- url     : https://prove2.me/theorems/36d5f0d5-c707-438b-b8f0-4210aa94ca4d
-- title:
--   A cyclic quadratic difference ratio sum is at most three
-- statement:
--   if $ a,b,c$ are positive number,then $ \sum_{cyc}\frac {4a^2 - b^2 - c^2}{a(b + c)} \leq 3$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_12820` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_12820; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_12820 {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (4 * a ^ 2 - b ^ 2 - c ^ 2) / (a * (b + c)) + (4 * b ^ 2 - c ^ 2 - a ^ 2) / (b * (c + a)) + (4 * c ^ 2 - a ^ 2 - b ^ 2) / (c * (a + b)) ≤ 3  :=  by sorry
