-- Prove2me | Theorems.Thm_WorkbookSource_base_34373
-- name    : WorkbookSource.base_34373
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T04:47:18.535984+00:00
-- url     : https://prove2.me/theorems/d750df21-260b-4fa2-a0d5-7d56f34ae5bf
-- title:
--   A comparison of weighted linear reciprocal sums
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that:
--   $$\frac{1}{a+2b}+\frac{1}{b+2c}+\frac{1}{c+2a}\geq4\left(\frac{1}{3a+4b+5c}+\frac{1}{3b+4c+5a}+\frac{1}{3c+4a+5b}\right).$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_34373` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_34373; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_34373 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / (a + 2 * b) + 1 / (b + 2 * c) + 1 / (c + 2 * a)) ≥ 4 * (1 / (3 * a + 4 * b + 5 * c) + 1 / (3 * b + 4 * c + 5 * a) + 1 / (3 * c + 4 * a + 5 * b))  :=  by sorry
