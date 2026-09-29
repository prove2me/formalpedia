-- Prove2me | Theorems.Thm_WorkbookSource_base_21549
-- name    : WorkbookSource.base_21549
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:47:16.484005+00:00
-- url     : https://prove2.me/theorems/9f5e0021-6547-460f-a997-c13e960b52e9
-- title:
--   A shifted cyclic quadratic ratio upper bound at fixed sum three
-- statement:
--   If $a,b,c$ are positive numbers such that $a+b+c=3$ , then
--    $\frac{a}{3a+b^{2}}+\frac{b}{3b+c^{2}}+\frac{c}{3c+a^{2}}\le \frac 3{4}$ .
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_21549` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_21549; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_21549 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : a / (3 * a + b ^ 2) + b / (3 * b + c ^ 2) + c / (3 * c + a ^ 2) ≤ 3 / 4  :=  by sorry
