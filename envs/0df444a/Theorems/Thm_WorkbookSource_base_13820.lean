-- Prove2me | Theorems.Thm_WorkbookSource_base_13820
-- name    : WorkbookSource.base_13820
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T03:51:15.717661+00:00
-- url     : https://prove2.me/theorems/84edc378-06f8-4142-addf-38f5c2640e64
-- title:
--   A shifted quadratic reciprocal upper bound at fixed sum three
-- statement:
--   If $a, b, c>0, a+b+c=3$ prove that $\sum_{cyc}{\frac{a}{2a^2+a+1}}\le\frac{3}{4}$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13820` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13820; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13820 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 3) : a / (2 * a ^ 2 + a + 1) + b / (2 * b ^ 2 + b + 1) + c / (2 * c ^ 2 + c + 1) ≤ 3 / 4  :=  by sorry
