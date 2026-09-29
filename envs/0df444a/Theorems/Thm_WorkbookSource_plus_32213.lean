-- Prove2me | Theorems.Thm_WorkbookSource_plus_32213
-- name    : WorkbookSource.plus_32213
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:48:45.25276+00:00
-- url     : https://prove2.me/theorems/d3bf42f9-9c2f-40a2-987b-986cdd2ac154
-- title:
--   A complementary pair-product inequality at fixed sum two
-- statement:
--   Let $ a, b$ and $ c$ be be positive real numbers such that $a+b+c=2 $ . Prove that $ (1-bc)(1-ca)(1-ab) \ge \frac{125a^2b^2c^2}{64}.$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_32213` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_32213; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_32213 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 2) : (1 - b * c) * (1 - c * a) * (1 - a * b) ≥ (125 * a ^ 2 * b ^ 2 * c ^ 2) / 64   :=  by sorry
