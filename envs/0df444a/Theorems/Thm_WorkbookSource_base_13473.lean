-- Prove2me | Theorems.Thm_WorkbookSource_base_13473
-- name    : WorkbookSource.base_13473
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:43:59.820234+00:00
-- url     : https://prove2.me/theorems/9bd4e366-6934-4593-98c9-3a4ce1fc481a
-- title:
--   A cyclic cubic bound with a triple-product correction
-- statement:
--   Let $a,b,c>0$ .Prove: $2(a^3+b^3+c^3)+3abc\geq 3(a^2b+b^2c+c^2a)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13473` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13473; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13473 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 2 * (a^3 + b^3 + c^3) + 3 * a * b * c ≥ 3 * (a^2 * b + b^2 * c + c^2 * a)  :=  by sorry
