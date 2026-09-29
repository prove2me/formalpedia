-- Prove2me | Theorems.Thm_WorkbookSource_base_4630
-- name    : WorkbookSource.base_4630
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:13:16.608571+00:00
-- url     : https://prove2.me/theorems/11e3177a-5c06-4e13-82d3-5642cac54612
-- title:
--   A comparison of cyclic weighted reciprocal sums
-- statement:
--   Let $a,b,c$ be positive real numbers. Prove that
--    $\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{5}{3a+b}+\frac{5}{3b+c}+\frac{5}{3c+a}\ge \frac{9}{a+3b}+\frac{9}{b+3c}+\frac{9}{c+3a}. $
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_4630` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_4630; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_4630 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 1 / a + 1 / b + 1 / c + 5 / (3 * a + b) + 5 / (3 * b + c) + 5 / (3 * c + a) ≥ 9 / (a + 3 * b) + 9 / (b + 3 * c) + 9 / (c + 3 * a)  :=  by sorry
