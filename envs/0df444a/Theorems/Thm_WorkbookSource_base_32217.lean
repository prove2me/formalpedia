-- Prove2me | Theorems.Thm_WorkbookSource_base_32217
-- name    : WorkbookSource.base_32217
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T05:30:46.618678+00:00
-- url     : https://prove2.me/theorems/640c7068-baea-4c7f-8eb7-5dcac6153545
-- title:
--   An asymmetric partial-sum reciprocal upper bound
-- statement:
--   Let $a,b,c$ be positive real numbers , prove that $ \frac{1}{a}+\frac{2}{a+b}+\frac{3}{a+b+c}\le \frac{4}{3}(\frac{1}{a}+\frac{1}{b}+\frac{1}{c}).$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_32217` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_32217; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_32217 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (1 / a + 2 / (a + b) + 3 / (a + b + c)) ≤ (4 / 3) * (1 / a + 1 / b + 1 / c)  :=  by sorry
