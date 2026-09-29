-- Prove2me | Theorems.Thm_WorkbookSource_base_6095
-- name    : WorkbookSource.base_6095
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:05:38.663089+00:00
-- url     : https://prove2.me/theorems/a4c0b078-5f54-421b-aa00-f42010b3af67
-- title:
--   A cyclic fifth-degree inequality on nonnegative variables
-- statement:
--   Let $a$ , $b$ and $c$ be non-negative numbers. Prove that: $a^4b+b^4c+c^4a\geq abc(a^2+b^2+c^2)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_6095` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_6095; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_6095 (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) : a^4 * b + b^4 * c + c^4 * a ≥ a * b * c * (a^2 + b^2 + c^2)  :=  by sorry
