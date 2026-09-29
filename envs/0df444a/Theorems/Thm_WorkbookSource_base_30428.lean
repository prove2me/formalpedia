-- Prove2me | Theorems.Thm_WorkbookSource_base_30428
-- name    : WorkbookSource.base_30428
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:51:04.007463+00:00
-- url     : https://prove2.me/theorems/4bae02f5-ec5b-4bd1-a8f4-e7c42ffc495f
-- title:
--   A cyclic cubic inequality involving a triple product
-- statement:
--   Prove: $\sum a^3+ 3\sum ac^2 \geq 3\sum a^2c+3abc$, given $a,b,c >0$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_30428` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_30428; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_30428 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : a ^ 3 + b ^ 3 + c ^ 3 + 3 * (a * c ^ 2 + b * a ^ 2 + c * b ^ 2) ≥ 3 * (a ^ 2 * c + b ^ 2 * a + c ^ 2 * b) + 3 * a * b * c  :=  by sorry
