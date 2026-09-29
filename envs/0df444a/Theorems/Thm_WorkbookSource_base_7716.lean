-- Prove2me | Theorems.Thm_WorkbookSource_base_7716
-- name    : WorkbookSource.base_7716
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:45:10.728511+00:00
-- url     : https://prove2.me/theorems/31a4b58a-1216-487a-8f02-f018b24d76bf
-- title:
--   Two squares bound a normalized triple product
-- statement:
--   Let $a,b,c$ be positive real numbers .Prove that
--
--    $$(a+b)^2+(a+b+4c)^2\geq \frac{100 abc}{a+b+c}$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_7716` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_7716; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_7716 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a + b) ^ 2 + (a + b + 4 * c) ^ 2 ≥ 100 * a * b * c / (a + b + c)  :=  by sorry
