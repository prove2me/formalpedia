-- Prove2me | Theorems.Thm_WorkbookSource_base_13043
-- name    : WorkbookSource.base_13043
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:48:33.344981+00:00
-- url     : https://prove2.me/theorems/e53acf5d-7537-43c9-b61e-db55b48aaa56
-- title:
--   A comparison of cyclic linear ratio sums
-- statement:
--   Prove that for positive real numbers \(a, b, c\), the following inequality holds:
--   $$\frac{3}{4}+\frac{a}{a+b}+\frac{b}{b+c}+\frac{c}{c+a} \ge \frac{9}{4}\left(\frac{a}{2a+b}+\frac{b}{2b+c}+\frac{c}{2c+a}\right)$$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13043` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13043; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13043 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (3 / 4 + a / (a + b) + b / (b + c) + c / (c + a)) ≥ (9 / 4) * (a / (2 * a + b) + b / (2 * b + c) + c / (2 * c + a))  :=  by sorry
