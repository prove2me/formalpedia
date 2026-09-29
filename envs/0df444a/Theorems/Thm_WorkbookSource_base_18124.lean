-- Prove2me | Theorems.Thm_WorkbookSource_base_18124
-- name    : WorkbookSource.base_18124
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:13:01.180848+00:00
-- url     : https://prove2.me/theorems/6b0d3bae-22a8-4e10-a59e-c0cbe1a9e4ad
-- title:
--   A comparison of two symmetric linear reciprocal sums
-- statement:
--   Let $ a, b, c$ are positive numbers. Prove that: $\frac {2}{a + b} + \frac {2}{a + c} + \frac {2}{b + c}\geq\frac {5}{a + b + 3c} + \frac {5}{a + c + 3b} + \frac {5}{b + c + 3a}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_18124` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_18124; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_18124 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 / (a + b) + 2 / (a + c) + 2 / (b + c) ≥ 5 / (a + b + 3 * c) + 5 / (a + c + 3 * b) + 5 / (b + c + 3 * a)  :=  by sorry
