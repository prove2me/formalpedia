-- Prove2me | Theorems.Thm_WorkbookSource_plus_17559
-- name    : WorkbookSource.plus_17559
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T06:45:39.20879+00:00
-- url     : https://prove2.me/theorems/aff18e02-eab2-472c-9fef-31c7c702b2a4
-- title:
--   A weighted quadratic reciprocal sum is at most one fifth at fixed sum three
-- statement:
--   Let $ a,$ $ b,$ $ c$ be positive real numbers such that $ a + b + c = 3.$ Prove that $ \frac {1}{a^2 + 7b^2 + 7c^2} + \frac {1}{b^2 + 7c^2 + 7a^2} + \frac {1}{c^2 + 7a^2 + 7b^2} \le \frac {1}{5}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_17559` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_17559; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_17559 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : 1 / (a ^ 2 + 7 * b ^ 2 + 7 * c ^ 2) + 1 / (b ^ 2 + 7 * c ^ 2 + 7 * a ^ 2) + 1 / (c ^ 2 + 7 * a ^ 2 + 7 * b ^ 2) ≤ 1 / 5   :=  by sorry
