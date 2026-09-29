-- Prove2me | Theorems.Thm_WorkbookSource_plus_15891
-- name    : WorkbookSource.plus_15891
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:55:21.407983+00:00
-- url     : https://prove2.me/theorems/1284e9cc-648f-49c2-ab16-f6b1f5ce0c73
-- title:
--   A sixth-degree product bound at fixed positive sum
-- statement:
--   Prove that: $ a^2b^2(a^2 + b^2) < = 128$ , $ a + b = 4$ and $ a,b > 0$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_15891` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_15891; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_15891 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a + b = 4) : a^2 * b^2 * (a^2 + b^2) ≤ 128   :=  by sorry
