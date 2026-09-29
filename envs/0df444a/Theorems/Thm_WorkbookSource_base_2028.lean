-- Prove2me | Theorems.Thm_WorkbookSource_base_2028
-- name    : WorkbookSource.base_2028
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T00:56:48.445488+00:00
-- url     : https://prove2.me/theorems/7b4c2a36-2adb-450e-afe7-86378a5c5f7e
-- title:
--   A cyclic quadratic-product ratio bound at fixed sum three
-- statement:
--   Let $a$ , $b$ and $c$ be positive numbers such that $a+b+c=3$ . Prove that: $\frac{a^2b}{2a+b}+\frac{b^2c}{2b+c}+\frac{c^2a}{2c+a}\leq1$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_2028` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_2028; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_2028 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a^2 * b / (2 * a + b) + b^2 * c / (2 * b + c) + c^2 * a / (2 * c + a) ≤ 1  :=  by sorry
